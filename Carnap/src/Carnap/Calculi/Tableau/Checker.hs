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
    , Typeable sem
    , Sequentable lex
    , PrismSubstitutionalVariable lex
    , EtaExpand (ClassicalSequentOver lex) sem
    ) => Tableau lex sem rule -> TreeFeedback
validateTree (Node n descendents) = Node (clean $ validateNode n theChildren) (map validateTree descendents)
    where theChildren = map rootLabel descendents
          clean (Correct:_) = Correct
          clean [Feedback s] = Feedback s
          clean [] = error "no feedback"

--TODO : catch eigenvariable errors in nodes
validateNode ::
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , FirstOrderLex (lex (ClassicalSequentOver lex))
    , Typeable sem
    , Sequentable lex
    , PrismSubstitutionalVariable lex
    , EtaExpand (ClassicalSequentOver lex) sem
    ) => TableauNode lex sem rule -> [TableauNode lex sem rule] -> [TreeFeedbackNode]
validateNode n ns = case hosolve [seqTarget n :=: seqRuleTarget n] of
                        Left (NoUnify _ _) -> return $ Feedback "Rule applied incorrectly to node" --TODO Improve feedback here
                        Right subs -> do sub <- subs
                                         childSeqs <- permutations (map tableauNodeSeq ns)
                                         let subbedChildren = map (applySub sub) (upperSequents theRule)
                                             subbedParent = applySub sub (lowerSequent theRule)
                                             prob = (subbedParent :=: tableauNodeSeq n) : zipWith (:=:) subbedChildren childSeqs
                                         case acuisolve prob of
                                             Left (NoUnify _ _) -> return $ Feedback "Rule applied incorrectly to branch" --TODO Improve feedback here.
                                             Right subs -> return Correct
    where theRule = schemeOf . tableauNodeRule $ n
          seqTarget :: Sequentable lex => TableauNode lex sem rule -> ClassicalSequentOver lex sem
          seqTarget = liftToSequent . tableauNodeTarget
          seqRuleTarget :: 
            ( Sequentable lex
            , PrismSubstitutionalVariable lex
            , FirstOrder (ClassicalSequentOver lex)
            , Typeable sem
            ) => TableauNode lex sem rule -> ClassicalSequentOver lex sem
          seqRuleTarget = liftToSequent . schemeTarget . schemeOf . tableauNodeRule

schemeTarget :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , Typeable sem
    , Sequentable lex
    , PrismSubstitutionalVariable lex
    ) => SequentRule lex sem -> FixLang lex sem
schemeTarget r = case filter isVar . toListOf concretes . lowerSequent $ r of
                 [f] -> fromSequent f
                 _ -> error $ "rule lacks a unique target"

schemeOf = undefined

ruleChildren = undefined

