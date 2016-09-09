{-#LANGUAGE GADTs, TypeOperators, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequencePropProof, Feedback(..),seqUnify, parsePropProof) where

import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Control.Monad.State
import Data.Tree
import Data.Either
import Data.List
import Text.Parsec (parse, Parsec, ParseError, choice, try, string)

--------------------------------------------------------
--Deduction Data
--------------------------------------------------------

type PartialDeduction r lex = [Either ParseError (DeductionLine r lex (Form Bool))]

type Deduction r lex = [DeductionLine r lex (Form Bool)]

data Feedback lex = Feedback { finalresult :: Maybe (ClassicalSequentOver lex Sequent)
                             , lineresults :: [Either ProofErrorMessage (ClassicalSequentOver lex Sequent)]}

--------------------------------------------------------
--Main Functions
--------------------------------------------------------

-- TODO: handle a list of deductionlines which contains some parsing errors
{- | 
find the prooftree corresponding to *line n* in ded, where proof line numbers start at 1
-}
toProofTree :: (Inference r lex, Sequentable lex) => 
    Deduction r lex -> Int -> Either ProofErrorMessage (ProofTree r lex)
toProofTree ded n = case ded !! (n - 1)  of
          (AssertLine f r dpth deps) -> 
                do mapM checkDep deps
                   deps' <- mapM (\x -> toProofTree ded x) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
          (ShowLine f d) -> 
                do m <- matchShow
                   let (QedLine r _ deps) = ded !! m
                   mapM (checkDep $ m + 1) deps 
                   deps' <- mapM (\x -> toProofTree ded x) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where --for scanning, we ignore the depth of the QED line
                      checkDep m m' = takeRange m' m >>= scan . init
                      matchShow = let ded' = drop n ded in
                          case findIndex (qedAt d) ded' of
                              Nothing -> Left "Open subproof (no corresponding QED)"
                              Just m' -> isSubProof n (n + m' - 1)
                      isSubProof n m = let (h:t) = lineRange n m ded in
                          case and (map (\x -> depth x > depth h) t) of
                              False -> Left $ "Open subproof on lines" ++ show n ++ " to " ++ show m ++ " (no QED in this subproof)"
                              True -> Right (m + 1)
                      qedAt d (QedLine _ dpth _) = d == dpth
                      qedAt d _ = False
          (QedLine _ _ _) -> Left "A QED line cannot be cited as a justification" 
    where ln = length ded
          --line h is accessible from the end of the chunk if everything in
          --the chunk has depth greater than or equal to that of line h
          scan chunk@(h:_) =
              if and (map (\x -> depth h <= depth x) chunk)
                  then Right True
                  else Left "It looks like you're citing a line which is not in your subproof. If you're not, you may need to tidy up your proof."
          takeRange m' n' = 
              if n' <= m' 
                      then Left "Dependency is later than assertion"
                      else Right $ lineRange m' n' ded
          --sublist, given by line numbers
          lineRange m n l = drop (m - 1) $ take n l

toDisplaySequencePropProof :: (MonadVar (ClassicalSequentOver lex) (State Int), Inference r lex, Sequentable lex) => 
    (String -> PartialDeduction r lex) -> String -> Feedback lex
toDisplaySequencePropProof topd s = if isParsed 
                                   then let feedback = map (processLine(rights ded)) [1 .. length ded] in
                                       Feedback (lastTopInd >>= fromFeedback feedback) feedback
                                   else Feedback Nothing (map handle ded)
    where ded = topd s
          isParsed = null $ lefts ded 
          handle (Left e) = Left $ "parsing error:" ++ show e
          handle (Right _) = Left ""
          isTop x = case x of
            (Right (AssertLine _ _ 0 _)) -> True
            (Right (ShowLine _ 0)) -> True
            _ -> False
          lastTopInd = do i <- findIndex isTop (reverse ded)
                          return $ length ded - i
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s
          processLine :: (Sequentable lex, Inference r lex, MonadVar (ClassicalSequentOver lex) (State Int)) => 
            [DeductionLine r lex (Form Bool)] -> Int -> Either ProofErrorMessage (ClassicalSequentOver lex Sequent)
          processLine ded n = case ded !! (n - 1) of
            --special case to catch QedLines not being cited in justifications
            (QedLine _ _ _) -> Left ""
            _ -> toProofTree ded n >>= firstLeft . reduceProofTree
          firstLeft (Left (x:xs)) = Left x
          firstLeft (Right x) = Right x
          --
-- | A simple check of whether two sequents can be unified
seqUnify s1 s2 = case check of
                     Left _ -> False
                     Right [] -> False
                     Right _ -> True
            where check = do fosub <- fosolve [rhs s1 :=: rhs s2]
                             acuisolve [lhs (applySub fosub s1) :=: lhs (applySub fosub s2)]


--------------------------------------------------------
--Logics
--------------------------------------------------------

data PropLogic = MP | MT | DNE | DNI | DD | AX | CP1 | CP2 | ID1 | ID2 | ID3
               deriving Show

instance Inference PropLogic PurePropLexicon where
    premisesOf MP  = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                     , GammaV 2 :|-: SS (SeqPhi 1)
                     ]
    premisesOf MT  = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                     , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf AX  = []
    premisesOf DD  = [ GammaV 1 :|-: SS (SeqPhi 1) ]
    premisesOf DNE = [ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) ]
    premisesOf DNI = [ GammaV 1 :|-: SS (SeqPhi 1) ]
    premisesOf CP1 = [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) ]
    premisesOf CP2 = [ GammaV 1 :|-: SS (SeqPhi 2) ]
    premisesOf ID1 = [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                     , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID2 = [ GammaV 1  :|-: SS (SeqPhi 2) 
                     , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID3 = [ GammaV 1  :|-: SS (SeqPhi 2) 
                     , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                     ]

    conclusionOf MP  = (GammaV 1 :+: GammaV 2) :|-: SS (SeqPhi 2)
    conclusionOf MT  = (GammaV 1 :+: GammaV 2) :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf AX  = SA (SeqPhi 1) :|-: SS (SeqPhi 1)
    conclusionOf DD  = GammaV 1 :|-: SS (SeqPhi 1) 
    conclusionOf DNE = GammaV 1 :|-: SS (SeqPhi 1) 
    conclusionOf DNI = GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) 
    conclusionOf CP1 = GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2) 
    conclusionOf CP2 = GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
    conclusionOf ID1 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf ID2 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
    conclusionOf ID3 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)

parsePropLogic :: Parsec String u [PropLogic]
parsePropLogic = do r <- choice (map (try . string) ["AS","PR","MP","MT","DD","DNE","DNI", "DN", "CD", "ID"])
                    case r of
                        "AS"  -> return [AX]
                        "PR"  -> return [AX]
                        "MP"  -> return [MP]
                        "MT"  -> return [MT]
                        "DD"  -> return [DD]
                        "DNE" -> return [DNE]
                        "DNI" -> return [DNI]
                        "DN"  -> return [DNE,DNI]
                        "CD"  -> return [CP1,CP2]
                        "ID"  -> return [ID1,ID2,ID3]

parsePropProof :: String -> [Either ParseError (DeductionLine PropLogic PurePropLexicon (Form Bool))]
parsePropProof = toDeduction parsePropLogic prePurePropFormulaParser


--------------------------------------------------------
--Utility Functions
--------------------------------------------------------

firstRight :: [Either a [b]] -> Either [a] b
firstRight xs = case filter isRight xs of
                    [] -> Left $ map (\(Left x) -> x) xs
                    (Right (r:x):rs) -> Right r
    where isRight (Right _) = True
          isRight _ = False

--Given a list of concrete rules and a list of (variable-free) premise sequents, and a (variable-free) 
--conclusion succeedent, return an error or a list of possible (variable-free) correct 
--conclusion sequents
seqFromNode :: (Inference r lex, MaybeMonadVar (ClassicalSequentOver lex) (State Int),
        MonadVar (ClassicalSequentOver lex) (State Int)) =>  
    [r] -> [ClassicalSequentOver lex Sequent] -> ClassicalSequentOver lex Succedent 
      -> [Either ProofErrorMessage [ClassicalSequentOver lex Sequent]]
seqFromNode rules prems conc = do rrule <- rules
                                  rprems <- permutations (premisesOf rrule) 
                                  return $ oneRule rrule rprems
    where oneRule r rp = do if length rp /= length prems 
                                then Left "Wrong number of premises"
                                else Right ""
                            let rconc = conclusionOf r
                            fosub <- fosolve 
                               (zipWith (:=:) 
                                   (map rhs (rconc:rp)) 
                                   (conc:map rhs prems))
                            let subbedrule = map (applySub fosub) rp
                            let subbedconc = applySub fosub rconc
                            acuisubs <- acuisolve 
                               (zipWith (:=:) 
                                   (map lhs subbedrule) 
                                   (map lhs prems))
                            return $ map (\x -> applySub x subbedconc) acuisubs

reduceProofTree :: (Inference r lex, 
                   MaybeMonadVar (ClassicalSequentOver lex) (State Int),
        MonadVar (ClassicalSequentOver lex) (State Int)) =>  
        ProofTree r lex -> Either [ProofErrorMessage] (ClassicalSequentOver lex Sequent)
reduceProofTree (Node (ProofLine no cont rule) ts) =  
        do prems <- mapM reduceProofTree ts
           firstRight $ seqFromNode rule prems cont
               -- TODO: label errors with lineNo

fosolve :: (FirstOrder (ClassicalSequentOver lex), MonadVar (ClassicalSequentOver lex) (State Int)) =>  
    [Equation (ClassicalSequentOver lex)] -> Either ProofErrorMessage [Equation (ClassicalSequentOver lex)]
fosolve eqs = case evalState (foUnifySys (const False) eqs) (0 :: Int) of 
                [] -> Left $ "The matching required to apply this rule here can't be done"
                [s] -> Right s

acuisolve :: (ACUI (ClassicalSequentOver lex), MonadVar (ClassicalSequentOver lex) (State Int)) =>  
    [Equation (ClassicalSequentOver lex)] -> Either ProofErrorMessage [[Equation (ClassicalSequentOver lex)]]
acuisolve eqs = 
        case evalState (acuiUnifySys (const False) eqs) (0 :: Int) of
          [] -> Left $ "The matching required to apply this rule here can't be done."
          subs -> Right subs

rhs :: ClassicalSequentOver lex Sequent -> ClassicalSequentOver lex Succedent
rhs (x :|-: (Bot :-: y)) = rhs (x :|-: y)
rhs (_ :|-: y) = y 

lhs :: ClassicalSequentOver lex Sequent -> ClassicalSequentOver lex Antecedent
lhs (x :|-: _) = x
