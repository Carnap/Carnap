{-#LANGUAGE GADTs, KindSignatures, TypeOperators, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequence,toDisplaySequenceMemo, toDisplaySequenceStructured, processLineMontegue, processLineFitch, processLineHardegree, hoProcessLineHardegree, hoProcessLineHardegreeMemo, processLineStructuredFitch,processLineStructuredFitchHO, hoProcessLineFitchMemo, hoProcessLineFitch, hoProcessLineMontegue, hoProcessLineMontegueMemo, hosolve, ProofErrorMessage(..), Feedback(..),seqUnify,seqSubsetUnify, toDeduction) where

import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (rebuild)
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.Huet
import Carnap.Core.Unification.ACUI
import Carnap.Languages.ClassicalSequent.Syntax
import Control.Lens
import Control.Monad.State
import Data.Tree (Tree(Node))
import Data.IORef
import Data.Either
import Data.List
import Data.Typeable
import Data.Hashable
import qualified Data.Map.Strict as M
import Data.Maybe (isNothing)

--------------------------------------------------------
--Main Functions
--------------------------------------------------------

-- XXX Clean this up and reduce duplication

toDisplaySequence:: 
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , Inference r lex sem, Sequentable lex
    ) =>  (Deduction r lex sem -> Restrictor r lex -> Int ->   FeedbackLine lex sem) 
            -> Deduction r lex sem -> Feedback lex sem
toDisplaySequence pl ded = let feedback = map (pl ded res) [1 .. length ded] in
                                  Feedback (lastTopInd >>= fromFeedback feedback) feedback
                          
    where isTop  (AssertLine _ _ 0 _) = True
          isTop  (ShowLine _ 0) = True
          isTop  (ShowWithLine _ 0 _ _) = True
          isTop  _ = False
          lastTopInd = do i <- findIndex isTop (reverse ded)
                          return $ length ded - i
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s
          res = globalRestriction (Left ded)

toDisplaySequenceMemo :: 
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , Inference r lex sem, Sequentable lex
    ) =>  (Deduction r lex sem -> Restrictor r lex -> Int ->  IO (FeedbackLine lex sem)) 
            -> Deduction r lex sem -> IO (Feedback lex sem)
toDisplaySequenceMemo pl ded = 
        do feedback <- mapM (pl ded res) [1 .. length ded]
           return $ Feedback (lastTopInd >>= fromFeedback feedback) feedback
                          
    where isTop  (AssertLine _ _ 0 _) = True
          isTop  (ShowLine _ 0) = True
          isTop  (ShowWithLine _ 0 _ _) = True
          isTop  _ = False
          lastTopInd = do i <- findIndex isTop (reverse ded)
                          return $ length ded - i
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s
          res = globalRestriction (Left ded)

toDisplaySequenceStructured:: 
    ( MonadVar (ClassicalSequentOver lex) (State Int)
    , Inference r lex sem, Sequentable lex
    ) =>  (DeductionTree r lex sem -> Restrictor r lex -> Int  -> FeedbackLine lex sem) -> DeductionTree r lex sem -> Feedback lex sem
toDisplaySequenceStructured pl ded@(SubProof (1,m) ls) = let feedback = map (pl ded res) [1 .. m] in
                                  Feedback (lastTopInd >>= fromFeedback feedback) feedback
                          
    where lastTopInd = case filter (\x -> case x of Leaf _ _ -> True; _ -> False) ls of
                           [] -> Nothing
                           ls -> Just $ (\(Leaf n _) -> n) $ last ls
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s
          res = globalRestriction (Right ded)


processLineHardegree :: 
  ( Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  ) => Deduction r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
processLineHardegree ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeHardegree ded n >>= reduceProofTree res

hoProcessLineHardegree :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , MaybeStaticVar (lex (ClassicalSequentOver lex))
  ) => Deduction r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
hoProcessLineHardegree ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeHardegree ded n >>= hoReduceProofTree res

hoProcessLineHardegreeMemo :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , MaybeStaticVar (lex (ClassicalSequentOver lex))
  , Show (ClassicalSequentOver lex (Succedent sem)), Show r
  ) => ProofMemoRef lex sem r -> Deduction r lex sem -> Restrictor r lex -> Int -> IO (FeedbackLine lex sem)
hoProcessLineHardegreeMemo ref ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> return $ Left $ NoResult n
  _ -> case toProofTreeHardegree ded n of
        Right t -> hoReduceProofTreeMemo ref res t 
        Left e -> return $ Left e

processLineMontegue :: 
  ( Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  ) => Deduction r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
processLineMontegue ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeMontegue ded n >>= reduceProofTree res
  
hoProcessLineMontegue :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , MaybeStaticVar (lex (ClassicalSequentOver lex))
  ) => Deduction r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
hoProcessLineMontegue ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeMontegue ded n >>= hoReduceProofTree res

hoProcessLineMontegueMemo :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , MaybeStaticVar (lex (ClassicalSequentOver lex))
  , Show (ClassicalSequentOver lex (Succedent sem)), Show r
  ) => ProofMemoRef lex sem r -> Deduction r lex sem -> Restrictor r lex -> Int -> IO (FeedbackLine lex sem)
hoProcessLineMontegueMemo ref ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> return $ Left $ NoResult n
  _ -> case toProofTreeMontegue ded n of
        Right t -> hoReduceProofTreeMemo ref res t
        Left e -> return $ Left e

processLineFitch :: 
  ( Sequentable lex
  , Inference r lex sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , Typeable sem
  ) => Deduction r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
processLineFitch ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeFitch ded n >>= reduceProofTree res

hoProcessLineFitch :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Typeable sem
  , Inference r lex sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , MaybeStaticVar (lex (ClassicalSequentOver lex))
  ) => Deduction r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
hoProcessLineFitch ded res n = case ded !! (n - 1) of
  --special case to catch QedLines not being cited in justifications
  (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeFitch ded n >>= hoReduceProofTree res

hoProcessLineFitchMemo :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , MaybeStaticVar (lex (ClassicalSequentOver lex))
  , Show (ClassicalSequentOver lex (Succedent sem)), Show r
  ) => ProofMemoRef lex sem r -> Deduction r lex sem -> Restrictor r lex -> Int -> IO (FeedbackLine lex sem)
hoProcessLineFitchMemo ref ded res n = case ded !! (n - 1) of
  (QedLine _ _ _) -> return $ Left $ NoResult n
  _ -> case toProofTreeFitch ded n of
        Right t -> hoReduceProofTreeMemo ref res t
        Left e -> return $ Left e

processLineStructuredFitch :: 
  ( Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  ) => DeductionTree r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
processLineStructuredFitch ded res n = case ded .! n of
  --special case to catch QedLines not being cited in justifications
  Just (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeStructuredFitch ded n >>= reduceProofTree res

processLineStructuredFitchHO :: 
  ( StaticVar (ClassicalSequentOver lex)
  , Sequentable lex
  , Inference r lex sem
  , Typeable sem
  , MonadVar (ClassicalSequentOver lex) (State Int)
  , MaybeStaticVar (lex (ClassicalSequentOver lex))
  ) => DeductionTree r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
processLineStructuredFitchHO ded res n = case ded .! n of
  --special case to catch QedLines not being cited in justifications
  Just (QedLine _ _ _) -> Left $ NoResult n
  _ -> toProofTreeStructuredFitch ded n >>= hoReduceProofTree res

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
          errFrom xs = case firstNonUni xs of
                               Nothing -> NoUnify (concat $ map eqsOf xs) lineno
                               Just err -> err

          firstNonUni [] = Nothing
          firstNonUni ((Left (NoUnify _ _)):ys) = firstNonUni ys
          firstNonUni ((Left y):_) = Just y

--Given a list of concrete rules and a list of (schematic-variable-free)
--premise sequents, and a (schematic-variable-free) conclusion succeedent,
--return an error or a list of possible (schematic-variable-free) correct
--conclusion sequents

foseqFromNode :: 
    ( Inference r lex sem
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    , Typeable sem
    ) =>  Int -> [r] -> [ClassicalSequentOver lex (Sequent sem)] -> ClassicalSequentOver lex (Succedent sem)
              -> Restrictor r lex
              -> [Either (ProofErrorMessage lex) [ClassicalSequentOver lex (Sequent sem)]]
foseqFromNode lineno rules prems conc res = 
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
    ( Inference r lex sem
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    , StaticVar (ClassicalSequentOver lex)
    , MaybeStaticVar (lex (ClassicalSequentOver lex))
    , Typeable sem
    ) =>  Int -> [r] -> [ClassicalSequentOver lex (Sequent sem)] -> ClassicalSequentOver lex (Succedent sem)
              -> [Either (ProofErrorMessage lex) 
                         [( ClassicalSequentOver lex (Sequent sem)
                          , [Equation (ClassicalSequentOver lex)]
                          , r
                          )]]
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
                                   case evalState (acuiUnifySys (const False) prob) (0 :: Int) of
                                       [] -> return $ Left $ renumber lineno $ NoUnify [prob] 0
                                       subs -> return $ Right $ map (\x -> (antecedentNub $ applySub x subbedconc,x,r)) (map (++ hosub) subs)

reduceProofTree :: 
    ( Inference r lex sem
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    , Typeable sem
    ) => Restrictor r lex -> ProofTree r lex sem ->  FeedbackLine lex sem
reduceProofTree res (Node (ProofLine no cont rules) ts) =  
        do prems <- mapM (reduceProofTree res) ts
           checkAgainst (res no rule) sub
           checkAgainst (restriction rule) sub
           reduceResult no $ foseqFromNode no rules prems cont res

hoReduceProofTree :: 
    ( Inference r lex sem
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    , StaticVar (ClassicalSequentOver lex)
    , MaybeStaticVar (lex (ClassicalSequentOver lex))
    , Typeable sem
    ) =>  Restrictor r lex -> ProofTree r lex sem -> FeedbackLine lex sem
hoReduceProofTree res (Node (ProofLine no cont rules) ts) =  
        do prems <- mapM (hoReduceProofTree res) ts
           (rslt, sub, rule) <- reduceResult no $ hoseqFromNode no rules prems cont 
           -- XXX: we need to rebuild the term here to make sure that there
           -- are no unevaluated substitutions lurking inside under
           -- lambdas, with stale variables in trapped in closures.
           checkAgainst (res no rule) sub
           checkAgainst (restriction rule) sub
           return $ rebuild $ evalState (toBNF (rebuild rslt)) (0 :: Int)

hoReduceProofTreeMemo :: 
    ( Inference r lex sem
    , MaybeMonadVar (ClassicalSequentOver lex) (State Int)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    , StaticVar (ClassicalSequentOver lex)
    , MaybeStaticVar (lex (ClassicalSequentOver lex))
    , Hashable (ProofTree r lex sem)
    , Typeable sem
    ) =>  ProofMemoRef lex sem r -> Restrictor r lex -> ProofTree r lex sem ->  IO (FeedbackLine lex sem)
hoReduceProofTreeMemo ref res pt@(Node (ProofLine no cont rules) ts) =  
        do thememo <- readIORef ref
           let thehash = hash pt
           case M.lookup thehash thememo of
               Just x -> return $ checkRestrictions x
               _      -> do prems <- mapM (hoReduceProofTreeMemo ref res) ts
                            let x = do prems' <- sequence prems 
                                       (rslt, sub, rule) <- reduceResult no $ hoseqFromNode no rules prems' cont
                                       let rslt' = rebuild $ evalState (toBNF (rebuild rslt)) (0 :: Int)
                                       return (rslt', sub, rule)
                            writeIORef ref (M.insert thehash x thememo)
                            return $ checkRestrictions x
    where checkRestrictions x = do (rslt, sub, rule) <- x
                                   checkAgainst (res no rule) sub
                                   checkAgainst (restriction rule) sub
                                   return rslt

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

checkAgainst (Just f) sub = case f sub of
                                  Nothing -> Right sub
                                  Just s -> Left $ GenericError s 0
checkAgainst Nothing sub = Right sub

