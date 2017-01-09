{-#LANGUAGE GADTs, KindSignatures, TypeOperators, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequence, processLine, processLineFitch, hoProcessLine, hosolve, ProofErrorMessage(..), Feedback(..),seqUnify,seqSubsetUnify, toDeduction) where

import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.Huet
import Carnap.Core.Unification.ACUI
import Carnap.Languages.ClassicalSequent.Syntax
import Control.Lens
import Control.Monad.State
import Data.Tree (Tree(Node))
import Data.Either
import Data.Maybe (isNothing)
import Data.List

--------------------------------------------------------
--Main Functions
--------------------------------------------------------

toDisplaySequence:: 
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , Inference r lex, Sequentable lex
    ) =>  (Deduction r lex -> Int -> FeedbackLine lex) -> Deduction r lex -> Feedback lex
toDisplaySequence pl ded = let feedback = map (pl ded) [1 .. length ded] in
                                  Feedback (lastTopInd >>= fromFeedback feedback) feedback
                          
    where isTop  (AssertLine _ _ 0 _) = True
          isTop  (ShowLine _ 0) = True
          isTop  _ = False
          lastTopInd = do i <- findIndex isTop (reverse ded)
                          return $ length ded - i
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s

processLine :: 
  ( Sequentable lex
  , Inference r lex
  , MonadVar (ClassicalSequentOver lex) (State Int)
  ) => Deduction r lex -> Int -> FeedbackLine lex
processLine ded n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTree ded n >>= reduceProofTree

processLineFitch :: 
  ( Sequentable lex
  , Inference r lex
  , MonadVar (ClassicalSequentOver lex) (State Int)
  ) => Deduction r lex -> Int -> FeedbackLine lex
processLineFitch ded n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeFitch ded n >>= reduceProofTree

hoProcessLine :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Inference r lex
  , MonadVar (ClassicalSequentOver lex) (State Int)
  ) => Deduction r lex -> Int -> FeedbackLine lex
hoProcessLine ded n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTree ded n >>= hoReduceProofTree

-- | A simple check of whether two sequents can be unified
seqUnify s1 s2 = case check of
                     Left _ -> False
                     Right [] -> False
                     Right _ -> True
            where check = do fosub <- fosolve [view lhs s1 :=: view rhs s2]
                             acuisolve [view lhs (applySub fosub s1) :=: view lhs (applySub fosub s2)]


-- TODO remove the need for this assumption.
-- | A simple check of whether one sequent unifies with a another, allowing
-- for weakening on the lhs; assumption is that neither side contains Delta -1
seqSubsetUnify s1 s2 = case check of
                       Left _ -> False
                       Right [] -> False
                       Right _ -> True
            where check = do fosub <- fosolve [view rhs s1 :=: view rhs s2]
                             acuisolve [(view lhs (applySub fosub s1) :+: GammaV (0 - 1)) :=: view lhs (applySub fosub s2) ]

--------------------------------------------------------
--Utility Functions
--------------------------------------------------------

reduceResult :: Int -> [Either (ProofErrorMessage lex) [b]] -> Either (ProofErrorMessage lex) b
reduceResult lineno xs = case rights xs of
                           [] -> Left $ errFrom xs
                           (r:x):rs -> Right r
    where eqsOf (Left (NoUnify eqs _)) = eqs
          errFrom xs@(Left x:_) = if and (map uni xs) 
                                     then NoUnify (concat $ map eqsOf xs) lineno
                                     else x
          uni (Left (NoUnify _ _)) = True
          uni _ = False

--Given a list of concrete rules and a list of (schematic-variable-free)
--premise sequents, and a (schematic-variable-free) conclusion succeedent,
--return an error or a list of possible (schematic-variable-free) correct
--conclusion sequents

foseqFromNode :: 
    ( Inference r lex
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) =>  Int -> [r] -> [ClassicalSequentOver lex Sequent] -> ClassicalSequentOver lex Succedent 
              -> [Either (ProofErrorMessage lex) [ClassicalSequentOver lex Sequent]]
foseqFromNode lineno rules prems conc = 
        do rrule <- rules
           rprems <- permutations (premisesOf rrule) 
           return $ oneRule rrule rprems
    where oneRule r rp = do if length rp /= length prems 
                                then Left $ GenericError "Wrong number of premises" lineno
                                else Right ""
                            let rconc = conclusionOf r
                            fosub <- fosolve 
                               (zipWith (:=:) 
                                   (map (view rhs) (rconc:rp)) 
                                   (conc:map (view rhs) prems))
                            let subbedrule = map (applySub fosub) rp
                            let subbedconc = applySub fosub rconc
                            acuisubs <- acuisolve 
                               (zipWith (:=:) 
                                   (map (view lhs) subbedrule) 
                                   (map (view lhs) prems))
                            return $ map (\x -> antecedentNub $ applySub x subbedconc) acuisubs

hoseqFromNode :: 
    ( Inference r lex
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) =>  Int -> [r] -> [ClassicalSequentOver lex Sequent] -> ClassicalSequentOver lex Succedent 
              -> [Either (ProofErrorMessage lex) [ClassicalSequentOver lex Sequent]]
hoseqFromNode lineno rules prems conc = 
        do r <- rules
           rps <- permutations (premisesOf r) 
           if length rps /= length prems 
                then return $ Left $ GenericError "Wrong number of premises" lineno
                else do let rconc = conclusionOf r
                        case hosolve (zipWith (:=:) 
                                        (map (view rhs) (rconc:rps)) 
                                        (conc:map (view rhs) prems)) of 
                            Left e -> return $ Left $ renumber lineno e 
                            Right hosubs -> 
                                do hosub <- hosubs
                                   let subbedrule = map (applySub hosub) rps
                                   let subbedconc = applySub hosub rconc
                                   let prob = (zipWith (:=:) (map (pureBNF . view lhs) subbedrule) 
                                                             (map (view lhs) prems))
                                   case hoacuisolve r hosub prob of 
                                     Right s -> return $ Right $ map (\x -> applySub x subbedconc) s
                                     Left e -> return $ Left $ renumber lineno e

reduceProofTree :: 
    ( Inference r lex
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) =>  ProofTree r lex -> Either (ProofErrorMessage lex) (ClassicalSequentOver lex Sequent)
reduceProofTree (Node (ProofLine no cont rules) ts) =  
        do prems <- mapM reduceProofTree ts
           reduceResult no $ foseqFromNode no rules prems cont

hoReduceProofTree :: 
    ( Inference r lex
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    , StaticVar (ClassicalSequentOver lex)
    ) =>  ProofTree r lex -> Either (ProofErrorMessage lex) (ClassicalSequentOver lex Sequent)
hoReduceProofTree (Node (ProofLine no cont rules) ts) =  
        do prems <- mapM hoReduceProofTree ts
           rslt <- reduceResult no $ hoseqFromNode no rules prems cont
           return $ evalState (toBNF rslt) (0 :: Int)

fosolve :: 
    ( FirstOrder (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) =>  [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [Equation (ClassicalSequentOver lex)]
fosolve eqs = case evalState (foUnifySys (const False) eqs) (0 :: Int) of 
                [] -> Left $ NoUnify [eqs] 0
                [s] -> Right s

hosolve :: 
    ( HigherOrder (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) => [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [[Equation (ClassicalSequentOver lex)]]
hosolve eqs = case evalState (huetUnifySys (const False) eqs) (0 :: Int) of
                    [] -> Left $ NoUnify [eqs] 0
                    subs -> Right subs

acuisolve :: 
    ( ACUI (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) => [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [[Equation (ClassicalSequentOver lex)]]
acuisolve eqs = 
        case evalState (acuiUnifySys (const False) eqs) (0 :: Int) of
          [] -> Left $ NoUnify [eqs] 0
          subs -> Right subs

hoacuisolve :: 
    ( Inference r lex
    , ACUI (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) =>  r -> [Equation (ClassicalSequentOver lex)] -> [Equation (ClassicalSequentOver lex)] 
            -> Either (ProofErrorMessage lex) [[Equation (ClassicalSequentOver lex)]]
hoacuisolve r sub1 eqs = 
        case evalState (acuiUnifySys (const False) eqs) (0 :: Int) of
          [] -> Left $ NoUnify [eqs] 0
          subs -> case restriction r of
                                Nothing -> Right subs
                                Just rst -> case partitionEithers $ checkAgainst rst subs of
                                           (s:_,[]) -> Left $ GenericError s 0
                                           (_,subs') -> Right subs'
    where checkAgainst f [] = []
          checkAgainst f (l:ls)  = case f (sub1 ++ l) of
                                     Nothing -> Right l : checkAgainst f ls
                                     Just s -> Left s : checkAgainst f ls
