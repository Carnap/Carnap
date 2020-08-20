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
    , SpecifiedUnificationType rule
    , CopulaSchema (FixLang lex)
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
validateTree :: SupportsTableau rule lex sem => Tableau lex sem rule -> TreeFeedback lex
validateTree (Node n descendents) = Node (clean $ validateNode n theChildren) (map validateTree descendents)
    where theChildren = map rootLabel descendents
          clean (Correct:_) = Correct
          clean (ProofData s:_) = ProofData s
          clean [ProofError e] = ProofError e
          clean (ProofError _ :xs) = clean xs
          clean _ = ProofData "no feedback"

validateNode :: SupportsTableau rule lex sem => TableauNode lex sem rule -> [TableauNode lex sem rule] -> [TreeFeedbackNode lex]
validateNode n ns = case tableauNodeRule n of
                        Nothing -> return $ treeErrMsg "no rule developing this node"
                        Just rs -> 
                            do r <- rs
                               let theRule = coreRuleOf r
                               if length (upperSequents theRule) /= length ns 
                               then return $ treeErrMsg "wrong number of premises"
                               else do
                                   ns' <- permutations ns
                                   let childSeqs = map tableauNodeSeq ns'
                                       thePairs = (lowerSequent theRule, n) : zip (upperSequents theRule) ns'
                                       addTarget (scheme,node) = (node, getTargets scheme)
                                       targetedPairs = map addTarget thePairs
                                   if any (not . lengthCheck) targetedPairs
                                       then return $ treeErrMsg "Missing target for rule"
                                       else do 
                                           let mainProb = concat . map (uncurry toEqs) $ targetedPairs
                                           case hosolve mainProb of
                                              Left e -> return $ ProofError e
                                              Right hosubs -> do
                                                  hosub <- hosubs
                                                  childSeqs <- permutations (map tableauNodeSeq ns)
                                                  let structsolver = case unificationType r of
                                                                       AssociativeUnification -> ausolve
                                                                       ACUIUnification -> acuisolve
                                                  let runSub = pureBNF . applySub hosub
                                                      subbedChildrenLHS = map (view lhs . runSub) (upperSequents theRule)
                                                      subbedChildrenRHS = map (view rhs . runSub) (upperSequents theRule)
                                                      subbedParentLHS = view lhs . runSub $ lowerSequent theRule
                                                      subbedParentRHS = view rhs . runSub $ lowerSequent theRule
                                                      prob = (subbedParentLHS :=: (view lhs . tableauNodeSeq $ n)) 
                                                           : (subbedParentRHS :=: (view rhs . tableauNodeSeq $ n))
                                                           : zipWith (:=:) subbedChildrenLHS (map (view lhs) childSeqs)
                                                           ++ zipWith (:=:) subbedChildrenRHS (map (view rhs) childSeqs)
                                                  case structsolver prob of
                                                    Left e -> return $ ProofError e
                                                    Right structsubs -> do 
                                                        finalsub <- map (++ hosub) structsubs
                                                        case coreRestriction r >>= ($ finalsub) of
                                                            Just msg -> return (treeErrMsg msg)
                                                            Nothing -> return Correct

getTargets ::  ClassicalSequentOver lex (Sequent sem) -> [SequentRuleTarget (ClassicalSequentLexOver lex) sem]
getTargets seq = let (linit,lremainder) = getInitTargetsLeft 1 ([], toListOf lhs seq)
                     (rinit,rremainder) = getInitTargetsRight 1 ([], toListOf rhs seq)
                     in linit ++ rinit ++ getTailTargetsLeft (-1) (reverse lremainder) ++ getTailTargetsRight (-1) (reverse rremainder)

getInitTargetsRight :: Int -> ([SequentRuleTarget (ClassicalSequentLexOver lex) sem], [ClassicalSequentOver lex (Succedent sem)]) 
                    -> ([SequentRuleTarget (ClassicalSequentLexOver lex) sem], [ClassicalSequentOver lex (Succedent sem)])
getInitTargetsRight n (acc, SS f : fs) = getInitTargetsRight (n+1) (RightTarget f n: acc, fs)
getInitTargetsRight n (acc, fs) = (acc, fs)

getInitTargetsLeft ::  Int -> ([SequentRuleTarget (ClassicalSequentLexOver lex) sem], [ClassicalSequentOver lex (Antecedent sem)]) 
                    -> ([SequentRuleTarget (ClassicalSequentLexOver lex) sem], [ClassicalSequentOver lex (Antecedent sem)])
getInitTargetsLeft n (acc, SA f : fs) = getInitTargetsLeft (n+1) (LeftTarget f n: acc, fs)
getInitTargetsLeft n (acc, fs) = (acc, fs)

getTailTargetsLeft ::  Int -> [ClassicalSequentOver lex (Antecedent sem)] -> [SequentRuleTarget (ClassicalSequentLexOver lex) sem]
getTailTargetsLeft n (SA f:fs) = LeftTarget f n : getTailTargetsLeft (n - 1) fs
getTailTargetsLeft n _ = []

getTailTargetsRight :: Int -> [ClassicalSequentOver lex (Succedent sem)] -> [SequentRuleTarget (ClassicalSequentLexOver lex) sem]
getTailTargetsRight n (SS f:fs)  = RightTarget f n: getTailTargetsRight (n - 1) fs
getTailTargetsRight n _ = []

lengthCheck (node,targets) = (minLengthLeft targets <= length (toListOf lhs (tableauNodeSeq node)))
                          && (minLengthRight targets <= length (toListOf rhs (tableauNodeSeq node))) 

--TODO: Beef this up to allow manual targeting
toEqs :: SupportsTableau rule lex sem => TableauNode lex sem rule -> [SequentRuleTarget (ClassicalSequentLexOver lex) sem] -> [Equation (ClassicalSequentOver lex)]
toEqs node target = 
    case target of
          (LeftTarget f n : ts)  | n > 0 -> intoEq f (theLHS !! (n - 1)) : toEqs node ts
          (LeftTarget f n : ts)  | 0 > n -> intoEq f (reverseLHS !! (abs n - 1)) : toEqs node ts
          (RightTarget f n : ts) | n > 0 -> intoEq f (theRHS !! (n - 1)) : toEqs node ts
          (RightTarget f n : ts) | 0 > n -> intoEq f (reverseRHS !! (abs n - 1)) : toEqs node ts
          (NoTarget : ts) -> toEqs node ts
          [] -> []

    where theLHS = toListOf (lhs . concretes) (tableauNodeSeq node)
          theRHS = toListOf (rhs . concretes) (tableauNodeSeq node) 
          reverseLHS = reverse theLHS
          reverseRHS = reverse theRHS
          intoEq f x = f :=: x

--the minimum length of a cedent given a set of Conc targets
minLengthLeft targets = minInit targets + abs (minTail targets)
    where minInit (LeftTarget _ n : ts) | n > 0 = max n (minInit ts)
          minInit _ = 0
          minTail (LeftTarget _ n : ts) | n < 0 = min n (minTail ts)
          minTail _ = 0

minLengthRight targets = minInit targets + abs (minTail targets)
    where minInit (RightTarget _ n : ts) | n > 0 = max n (minInit ts)
          minInit _ = 0
          minTail (RightTarget _ n : ts) | n < 0 = min n (minTail ts)
          minTail _ = 0

treeErrMsg :: String -> TreeFeedbackNode lex
treeErrMsg s = ProofError (GenericError s 0)

data SequentRuleTarget lex sem = LeftTarget (FixLang lex sem) Int --the Int gives the position of the target in the left cedent of the sequent
                               | RightTarget (FixLang lex sem) Int
                               | NoTarget

deriving instance Eq (FixLang lex sem) => Eq (SequentRuleTarget lex sem)
deriving instance Show (FixLang lex sem) => Show (SequentRuleTarget lex sem)
