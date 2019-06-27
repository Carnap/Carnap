{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.Tableau.Checker where

import Carnap.Core.Data.Types
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
          clean [] = error "no feedback"

validateNode ::
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , FirstOrderLex (lex (ClassicalSequentOver lex))
    , PrismLink (lex (ClassicalSequentOver lex)) (SubstitutionalVariable (ClassicalSequentOver lex)) -- XXX Not needed in GHC >= 8.4
    , Typeable sem
    , Sequentable lex
    , CoreInference rule lex sem
    , PrismSubstitutionalVariable lex
    , EtaExpand (ClassicalSequentOver lex) sem
    ) => TableauNode lex sem rule -> [TableauNode lex sem rule] -> [TreeFeedbackNode]
validateNode n ns = case tableauNodeRule n of
                        Nothing -> return $ Feedback "no rule developing this node"
                        Just r -> case hosolve [(liftToSequent  . tableauNodeTarget $ n) :=: (liftToSequent . schemeTarget . coreRuleOf $ r)] of
                            Left (NoUnify _ _) -> return $ Feedback "Rule applied incorrectly to node" --TODO Improve feedback here
                            Right subs -> do
                                sub <- subs
                                case coreRestriction r >>= ($ sub) of
                                    Just msg -> return $ Feedback msg
                                    Nothing -> do
                                      childSeqs <- permutations (map tableauNodeSeq ns)
                                      let theRule = coreRuleOf r
                                          subbedChildren = map (applySub sub) (upperSequents theRule)
                                          subbedParent = applySub sub (lowerSequent theRule)
                                          prob = (subbedParent :=: tableauNodeSeq n) : zipWith (:=:) subbedChildren childSeqs
                                      case acuisolve prob of
                                          Left (NoUnify _ _) -> return $ Feedback "Rule applied incorrectly to branch" --TODO Improve feedback here.
                                          Right subs -> return Correct

schemeTarget :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , Typeable sem
    , Sequentable lex
    , PrismSubstitutionalVariable lex
    ) => SequentRule lex sem -> FixLang lex sem
schemeTarget r = case filter isVar . toListOf concretes . lowerSequent $ r of
                 [f] -> fromSequent f
                 _ -> error $ "rule lacks a unique target"
