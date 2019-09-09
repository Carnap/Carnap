{-#LANGUAGE FlexibleContexts, StandaloneDeriving, UndecidableInstances, ConstraintKinds #-}
module Carnap.Calculi.Tableau.Checker where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util (hasVar)
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.ACUI
import Carnap.Calculi.Util
import Carnap.Calculi.Tableau.Data
import Carnap.Languages.ClassicalSequent.Syntax
import Data.Tree
import Data.List
import Data.Typeable
import Control.Monad.State
import Control.Lens

type SupportsTableau rule lex sem = 
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , FirstOrderLex (lex (ClassicalSequentOver lex))
    , FirstOrderLex (lex (FixLang lex))
    , Eq (FixLang lex sem)
    , Schematizable (lex (ClassicalSequentOver lex))
    , CopulaSchema (ClassicalSequentOver lex)
    , BoundVars lex
    , PrismLink (lex (ClassicalSequentOver lex)) (SubstitutionalVariable (ClassicalSequentOver lex)) -- XXX Not needed in GHC >= 8.4
    , Typeable sem
    , Sequentable lex
    , CoreInference rule lex sem
    , PrismSubstitutionalVariable lex
    , EtaExpand (ClassicalSequentOver lex) sem
    )

--This function should swap out the contents of each node in a tableau for
--appropriate feedback, or an indication that the node is correct.
validateTree :: SupportsTableau rule lex sem => Tableau lex sem rule -> TreeFeedback
validateTree (Node n descendents) = Node (clean $ validateNode n theChildren) (map validateTree descendents)
    where theChildren = map rootLabel descendents
          clean (Correct:_) = Correct
          clean [Feedback s] = Feedback s
          clean (Feedback _ :xs) = clean xs
          clean _ = Feedback "no feedback"

validateNode ::SupportsTableau rule lex sem => TableauNode lex sem rule -> [TableauNode lex sem rule] -> [TreeFeedbackNode]
validateNode n ns = case tableauNodeRule n of
                        Nothing -> return $ Feedback "no rule developing this node"
                        Just r -> 
                            do let theRule = coreRuleOf r
                               if length (upperSequents theRule) /= length ns 
                               then return $ Feedback "wrong number of premises"
                               else do
                                   ns' <- permutations ns
                                   let childSeqs = map tableauNodeSeq ns'
                                       intoEq f x = [f :=: x]
                                       maybeMainProb = concat <$> mapM (\t -> case t of
                                          NoTarget -> Just []
                                          RightPrem n f -> intoEq f <$> nodeTargetRight (ns' !! n)
                                          LeftPrem n f -> intoEq f <$> nodeTargetLeft (ns' !! n)
                                          LeftConc f -> intoEq f <$> nodeTargetLeft n
                                          RightConc f -> intoEq f <$> nodeTargetRight n) (schemeTargets theRule)
                                   case maybeMainProb of
                                       Nothing -> return $ Feedback "Missing target for rule"
                                       Just mainProb -> case hosolve mainProb of
                                            Left (NoUnify _ _) -> return $ 
                                                Feedback $ "Rule applied incorrectly to node: cannot unify\n\n " 
                                                        ++ unlines (map show mainProb)
                                            Right hosubs -> do
                                                hosub <- hosubs
                                                childSeqs <- permutations (map tableauNodeSeq ns)
                                                let runSub = pureBNF . applySub hosub
                                                    subbedChildrenLHS = map (view lhs . runSub) (upperSequents theRule)
                                                    subbedChildrenRHS = map (view rhs . runSub) (upperSequents theRule)
                                                    subbedParentLHS = view lhs . runSub $ lowerSequent theRule
                                                    subbedParentRHS = view rhs . runSub $ lowerSequent theRule
                                                    prob = (subbedParentLHS :=: (view lhs . tableauNodeSeq $ n)) 
                                                         : (subbedParentRHS :=: (view rhs . tableauNodeSeq $ n))
                                                         : zipWith (:=:) subbedChildrenLHS (map (view lhs) childSeqs)
                                                         ++ zipWith (:=:) subbedChildrenRHS (map (view rhs) childSeqs)
                                                case acuisolve prob of
                                                    Left (NoUnify _ _) -> return $ 
                                                      Feedback $ "Rule applied incorrectly to branch, cannot solve:\n\n"
                                                              ++ unlines (map show prob) 
                                                    Right acuisubs -> do 
                                                        finalsub <- map (++ hosub) acuisubs
                                                        case coreRestriction r >>= ($ finalsub) of
                                                            Just msg -> return $ Feedback msg
                                                            Nothing -> return Correct

nodeTargetLeft, nodeTargetRight :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , FirstOrderLex (lex (FixLang lex))
    , Typeable sem
    , Sequentable lex
    , BoundVars lex
    , PrismSubstitutionalVariable lex
    ) => TableauNode lex sem rule -> Maybe (ClassicalSequentOver lex sem)
nodeTargetLeft n = case (tableauNodeTarget n, toListOf concretes . view lhs . tableauNodeSeq $ n)  of
                     (Just f,_) -> Just $ liftToSequent f
                     (Nothing,[]) -> Nothing
                     (Nothing, l) -> Just $ last l
nodeTargetRight n = case (tableauNodeTarget n, toListOf concretes . view rhs . tableauNodeSeq $ n) of
                     (Just f,_) -> Just $ liftToSequent f
                     (Nothing,[]) -> Nothing
                     (Nothing, l) -> Just $ head l
  --head and last are reversed because `concretes` reverses order, I think

schemeTarget :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , Eq (ClassicalSequentOver lex sem)
    , FirstOrderLex (lex (FixLang lex))
    , Typeable sem
    , Sequentable lex
    , BoundVars lex
    , PrismSubstitutionalVariable lex
    ) => SequentRule lex sem -> SequentRuleTarget (ClassicalSequentLexOver lex) sem
schemeTarget r = case getTarget (lowerSequent r) of 
                    NoTarget -> case filter (\(_,x) -> x /= NoTarget) . map (\(n,x) -> (n,getTarget x)) . zip [0..] $ upperSequents r of
                                       [] -> NoTarget
                                       ((n,LeftConc f):_) -> LeftPrem n f
                                       ((n,RightConc f):_) -> RightPrem n f
                    target -> target

schemeTargets :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , Eq (FixLang lex sem)
    , FirstOrderLex (lex (FixLang lex))
    , Typeable sem
    , Sequentable lex
    , BoundVars lex
    , PrismSubstitutionalVariable lex
    ) => SequentRule lex sem -> [SequentRuleTarget (ClassicalSequentLexOver lex) sem]
schemeTargets r = redundant targetList []
    where targetList = getTarget (lowerSequent r) : map retarget (zip [0 ..] (map getTarget $ upperSequents r))
          retarget (n,LeftConc f) = LeftPrem n f
          retarget (n,RightConc f) = RightPrem n f
          retarget (_,NoTarget) = NoTarget
          redundant [] accum = accum
          redundant (NoTarget:potential) accum = redundant potential accum
          redundant (p:potential) accum | any (subform p) accum = redundant potential accum
                                        | otherwise = redundant potential  $ p : (filter (not . flip subform p) accum)
          subform x y = (targetContent x) `elem` universe (targetContent y)
          targetContent (LeftConc f) = fromSequent f
          targetContent (RightConc f) = fromSequent f
          targetContent (LeftPrem _ f) = fromSequent f
          targetContent (RightPrem _ f) = fromSequent f

getTarget seq = case ( filter (hasVar . fromSequent) . toListOf concretes . view lhs $ seq
             , filter (hasVar . fromSequent) . toListOf concretes . view rhs $ seq
             ) of (f:_,_) -> LeftConc f
                  (_,f:_) -> RightConc f
                  _ -> NoTarget

data SequentRuleTarget lex sem = LeftConc (FixLang lex sem) 
                               | RightConc (FixLang lex sem) 
                               | LeftPrem Int (FixLang lex sem)
                               | RightPrem Int (FixLang lex sem)
                               | NoTarget

deriving instance Eq (FixLang lex sem) => Eq (SequentRuleTarget lex sem)
