{-#LANGUAGE GADTs, KindSignatures, TypeOperators, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequence, hoToDisplaySequence, hosolve, ProofErrorMessage(..), Feedback(..),seqUnify,seqSubsetUnify, toDeduction) where

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
import Data.Tree
import Data.Either
import Data.Maybe (isNothing)
import Data.List
import Text.Parsec (parse, Parsec, ParseError, choice, try, string)

--------------------------------------------------------
--Deduction Data
--------------------------------------------------------

--type PartialDeduction r lex = [Either ParseError (DeductionLine r lex (Form Bool))]

type Deduction r lex = [DeductionLine r lex (Form Bool)]

data Feedback lex = Feedback { finalresult :: Maybe (ClassicalSequentOver lex Sequent)
                             , lineresults :: [Either (ProofErrorMessage lex) (ClassicalSequentOver lex Sequent)]}

data ProofErrorMessage :: ((* -> *) -> * -> *) -> * where
        NoParse :: ParseError -> Int -> ProofErrorMessage lex
        NoUnify :: [[Equation (ClassicalSequentOver lex)]]  -> Int -> ProofErrorMessage lex
        GenericError :: String -> Int -> ProofErrorMessage lex
        NoResult :: Int -> ProofErrorMessage lex --meant for blanks

lineNoOfError (NoParse _ n) = n
lineNoOfError (NoUnify _ n) = n
lineNoOfError (GenericError _ n) = n
lineNoOfError (NoResult n) = n

renumber :: Int -> ProofErrorMessage lex -> ProofErrorMessage lex
renumber m (NoParse x n) = NoParse x m
renumber m (NoUnify x n) = NoUnify x m
renumber m (GenericError s n) = GenericError s m
renumber m (NoResult n) = NoResult m

--------------------------------------------------------
--Main Functions
--------------------------------------------------------

-- TODO: handle a list of deductionlines which contains some parsing errors
-- XXX This is pretty ugly, and should be rewritten
{- | 
find the prooftree corresponding to *line n* in ded, where proof line numbers start at 1
-}
toProofTree :: 
    ( Inference r lex
    , Sequentable lex
    ) => Deduction r lex -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex)
toProofTree ded n = case ded !! (n - 1)  of
          (AssertLine f r dpth deps) -> 
                do mapM checkDep deps
                   deps' <- mapM (\x -> toProofTree ded x) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
          (ShowLine f d) -> 
                do m <- matchShow
                   let (QedLine r _ deps) = ded !! m
                   mapM_ (checkDep $ m + 1) deps 
                   deps' <- mapM (\x -> toProofTree ded x) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where --for scanning, we ignore the depth of the QED line
                      checkDep m m' = takeRange m' m >>= scan . init
                      matchShow = let ded' = drop n ded in
                          case findIndex (qedAt d) ded' of
                              Nothing -> err "Open subproof (no corresponding QED)"
                              Just m' -> isSubProof n (n + m' - 1)
                      isSubProof n m = case lineRange n m ded of
                        (h:t) -> if and (map (\x -> depth x > depth h) t) 
                                   then Right (m + 1)
                                   else  err $ "Open subproof on lines" ++ show n ++ " to " ++ show m ++ " (no QED in this subproof)"
                        []    -> Right (m+1)
                      qedAt d (QedLine _ dpth _) = d == dpth
                      qedAt d _ = False
          (QedLine _ _ _) -> err "A QED line cannot be cited as a justification" 
          (PartialLine _ e _) -> Left $ NoParse e n
    where -- XXX : inline this?
          err :: String -> Either (ProofErrorMessage lex) a
          err = \x -> Left $ GenericError x n
          ln = length ded
          --line h is accessible from the end of the chunk if everything in
          --the chunk has depth greater than or equal to that of line h,
          --and h is not a show line with no matching QED
          scan chunk@(h:t) =
              if and (map (\x -> depth h <= depth x) chunk)
                  then case h of
                    (ShowLine _ _) -> if or (map (\x -> depth h == depth x) t)
                        then Right True
                        else err "To cite a show line at this point, the line be available---it must have a matching QED earlier than this line."
                    _ -> Right True
                  else err "It looks like you're citing a line which is not in your subproof. If you're not, you may need to tidy up your proof."
          takeRange m' n' = 
              if n' <= m' 
                      then err "Dependency is later than assertion"
                      else Right $ lineRange m' n' ded
          --sublist, given by line numbers
          lineRange m n l = drop (m - 1) $ take n l

toDisplaySequence:: 
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , Inference r lex, Sequentable lex
    ) => (String -> Deduction r lex) -> String -> Feedback lex
toDisplaySequence tod s = let feedback = map (processLine ded) [1 .. length ded] in
                                  Feedback (lastTopInd >>= fromFeedback feedback) feedback
                          
    where ded = tod s
          isTop  (AssertLine _ _ 0 _) = True
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
            ) => [DeductionLine r lex (Form Bool)] -> Int -> Either (ProofErrorMessage lex) (ClassicalSequentOver lex Sequent)
          processLine ded n = case ded !! (n - 1) of
            --special case to catch QedLines not being cited in justifications
            (QedLine _ _ _) -> Left $ NoResult n
            _ -> toProofTree ded n >>= reduceProofTree

-- XXX Obviously find some way to reduce duplication here.
hoToDisplaySequence :: 
    ( StaticVar (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    , Inference r lex, Sequentable lex
    ) => (String -> Deduction r lex) -> String -> Feedback lex
hoToDisplaySequence tod s = let feedback = map (processLine ded) [1 .. length ded] in
                                  Feedback (lastTopInd >>= fromFeedback feedback) feedback
    where ded = tod s
          isTop  (AssertLine _ _ 0 _) = True
          isTop  (ShowLine _ 0) = True
          isTop  _ = False
          lastTopInd = do i <- findIndex isTop (reverse ded)
                          return $ length ded - i
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s
          processLine :: 
            ( StaticVar (ClassicalSequentOver lex)
            , Sequentable lex
            , Inference r lex
            , MonadVar (ClassicalSequentOver lex) (State Int)
            ) => [DeductionLine r lex (Form Bool)] -> Int -> Either (ProofErrorMessage lex) (ClassicalSequentOver lex Sequent)
          processLine ded n = case ded !! (n - 1) of
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
                        case hosolve (zipWith (:=:) (map (view rhs) (rconc:rps)) (conc:map (view rhs) prems)) of 
                            Left e -> return $ Left $ renumber lineno e 
                            Right hosubs -> 
                                do hosub <- hosubs
                                   let subbedrule = map (applySub hosub) rps
                                   let subbedconc = applySub hosub rconc
                                   let prob = (zipWith (:=:) (map (pureBNF . view lhs) subbedrule) 
                                                             (map (view lhs) prems))
                                   case hoacuisolve r hosub prob of Right s -> return $ Right $ map (\x -> applySub x subbedconc) s
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
