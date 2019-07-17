{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.Tableau.Checker where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
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

--This function should swap out the contents of each node in a tableau for
--appropriate feedback, or an indication that the node is correct.
validateTree :: 
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , FirstOrderLex (lex (ClassicalSequentOver lex))
    , FirstOrderLex (lex (FixLang lex))
    , Schematizable (lex (ClassicalSequentOver lex))
    , CopulaSchema (ClassicalSequentOver lex)
    , BoundVars lex
    , PrismLink (lex (ClassicalSequentOver lex)) (SubstitutionalVariable (ClassicalSequentOver lex)) -- XXX Not needed in GHC >= 8.4
    , Typeable sem
    , Sequentable lex
    , CoreInference rule lex sem
    , PrismSubstitutionalVariable lex
    , EtaExpand (ClassicalSequentOver lex) sem
    ) => Tableau lex sem rule -> TreeFeedback
validateTree (Node n descendents) = Node (clean $ validateNode n theChildren) (map validateTree descendents)
    where theChildren = map rootLabel descendents
          clean (Correct:_) = Correct
          clean [Feedback s] = Feedback s
          clean (Feedback _ :xs) = clean xs
          clean [] = error "no feedback"

validateNode ::
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , FirstOrderLex (lex (ClassicalSequentOver lex))
    , FirstOrderLex (lex (FixLang lex))
    , Schematizable (lex (ClassicalSequentOver lex))
    , CopulaSchema (ClassicalSequentOver lex)
    , BoundVars lex
    , PrismLink (lex (ClassicalSequentOver lex)) (SubstitutionalVariable (ClassicalSequentOver lex)) -- XXX Not needed in GHC >= 8.4
    , Typeable sem
    , Sequentable lex
    , CoreInference rule lex sem
    , PrismSubstitutionalVariable lex
    , EtaExpand (ClassicalSequentOver lex) sem
    ) => TableauNode lex sem rule -> [TableauNode lex sem rule] -> [TreeFeedbackNode]
validateNode n ns = case tableauNodeRule n of
                        Nothing -> return $ Feedback "no rule developing this node"
                        Just r -> let theTarget = schemeTarget . coreRuleOf $ r
                                      mainProb = [(getTarget theTarget) :=: (nodeTarget theTarget n)] in
                            case hosolve mainProb of
                                Left (NoUnify _ _) -> return $ 
                                    Feedback $ "Rule applied incorrectly to node: cannot unify " 
                                            ++ unlines (map show mainProb)
                                Right subs -> do
                                    sub <- subs
                                    case coreRestriction r >>= ($ sub) of
                                        Just msg -> return $ Feedback msg
                                        Nothing -> do
                                          childSeqs <- permutations (map tableauNodeSeq ns)
                                          let theRule = coreRuleOf r
                                              subbedChildrenLHS = map (view lhs . applySub sub) (upperSequents theRule)
                                              subbedChildrenRHS = map (view rhs . applySub sub) (upperSequents theRule)
                                              subbedParentLHS = view lhs . applySub sub $ lowerSequent theRule
                                              subbedParentRHS = view rhs . applySub sub $ lowerSequent theRule
                                              prob = (subbedParentLHS :=: (view lhs . tableauNodeSeq $ n)) 
                                                   : (subbedParentRHS :=: (view rhs . tableauNodeSeq $ n))
                                                   : zipWith (:=:) subbedChildrenLHS (map (view lhs) childSeqs)
                                                   ++ zipWith (:=:) subbedChildrenRHS (map (view rhs) childSeqs)
                                          case acuisolve prob of
                                              Left (NoUnify _ _) -> return $ 
                                                Feedback $ "Rule applied incorrectly to branch, cannot solve:\n\n"
                                                        ++ unlines (map show prob) 
                                              Right subs -> return Correct

nodeTarget :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , FirstOrderLex (lex (FixLang lex))
    , Typeable sem
    , Sequentable lex
    , BoundVars lex
    , PrismSubstitutionalVariable lex
    ) => SequentRuleTarget (ClassicalSequentLexOver lex) sem -> TableauNode lex sem rule -> ClassicalSequentOver lex sem
nodeTarget t n = case tableauNodeTarget n of
                     Just f -> liftToSequent f
                     Nothing -> case t of
                                    --head and last are reversed because `concretes` reverses order, I think
                                    RightConc _ -> head . toListOf concretes . view rhs . tableauNodeSeq $ n
                                    LeftConc _ -> last . toListOf concretes . view lhs . tableauNodeSeq $ n
                                    _ -> error "bad nodeTarget location"

schemeTarget :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , FirstOrderLex (lex (FixLang lex))
    , Typeable sem
    , Sequentable lex
    , BoundVars lex
    , PrismSubstitutionalVariable lex
    ) => SequentRule lex sem -> SequentRuleTarget (ClassicalSequentLexOver lex) sem
schemeTarget r = case ( filter (any isVar . universe . fromSequent) . toListOf concretes . view lhs . lowerSequent $ r
                      , filter (any isVar . universe . fromSequent) . toListOf concretes . view rhs . lowerSequent $ r
                      ) of (f:_,_) -> LeftConc f
                           (_,f:_) -> RightConc f
                           _ -> error $ "rule lacks a target."

data SequentRuleTarget lex sem = LeftConc (FixLang lex sem) 
                               | RightConc (FixLang lex sem) 
                               | LeftPrem Int (FixLang lex sem)
                               | RightPrem Int (FixLang lex sem)
                               | NoTarget

getTarget (LeftConc f) = f
getTarget (RightConc f) = f
getTarget (LeftPrem _ f) = f
getTarget (RightPrem _ f) = f
