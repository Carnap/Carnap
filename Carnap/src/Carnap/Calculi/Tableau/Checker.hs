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
                        Just r -> case hosolve [(liftToSequent . schemeTarget . coreRuleOf $ r) :=: (liftToSequent  . tableauNodeTarget $ n)] of
                            Left (NoUnify _ _) -> return $ 
                                Feedback $ "Rule applied incorrectly to node: cannot unify " 
                                        ++ show [(liftToSequent . schemeTarget . coreRuleOf $ r) :=: (liftToSequent  . tableauNodeTarget $ n)]
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
                                            Feedback $ "Rule applied incorrectly to branch, cannot solve"
                                                    ++ show prob
                                          Right subs -> return Correct

schemeTarget :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , FirstOrderLex (lex (FixLang lex))
    , Typeable sem
    , Sequentable lex
    , BoundVars lex
    , PrismSubstitutionalVariable lex
    ) => SequentRule lex sem -> FixLang lex sem
schemeTarget r = case filter (any isVar . universe . fromSequent) . toListOf concretes . lowerSequent $ r of
                 (f:_) -> fromSequent f
                 [] -> error $ "rule lacks a target."
