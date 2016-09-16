{-#LANGUAGE GADTs, KindSignatures, TypeOperators, FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequencePropProof, ProofErrorMessage(..), Feedback(..),seqUnify,seqSubsetUnify, parsePropProof) where

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

--------------------------------------------------------
--Main Functions
--------------------------------------------------------

-- TODO: handle a list of deductionlines which contains some parsing errors
-- XXX: This is pretty ugly, and should be rewritten
{- | 
find the prooftree corresponding to *line n* in ded, where proof line numbers start at 1
-}
toProofTree :: (Inference r lex, Sequentable lex) => 
    Deduction r lex -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex)
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
    where err :: String -> Either (ProofErrorMessage lex) a
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

toDisplaySequencePropProof :: (MonadVar (ClassicalSequentOver lex) (State Int), Inference r lex, Sequentable lex) => 
    (String -> PartialDeduction r lex) -> String -> Feedback lex
toDisplaySequencePropProof topd s = if isParsed 
                                   then let feedback = map (processLine(rights ded)) [1 .. length ded] in
                                       Feedback (lastTopInd >>= fromFeedback feedback) feedback
                                   else Feedback Nothing (zipWith handle ded [1 .. length ded])
    where ded = topd s
          isParsed = null $ lefts ded 
          handle (Left e) n = Left $ NoParse e n
          handle (Right _) n = Left $ NoResult n
          isTop (Right (AssertLine _ _ 0 _)) = True
          isTop  (Right (ShowLine _ 0)) = True
          isTop  _ = False
          lastTopInd = do i <- findIndex isTop (reverse ded)
                          return $ length ded - i
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s
          updateLine n (Right x) = Right x
          updateLine n (Left e) = Left e
          processLine :: (Sequentable lex, Inference r lex, MonadVar (ClassicalSequentOver lex) (State Int)) => 
            [DeductionLine r lex (Form Bool)] -> Int -> Either (ProofErrorMessage lex) (ClassicalSequentOver lex Sequent)
          processLine ded n = case ded !! (n - 1) of
            --special case to catch QedLines not being cited in justifications
            (QedLine _ _ _) -> Left $ NoResult n
            _ -> toProofTree ded n >>= (updateLine n . reduceProofTree)
          
-- | A simple check of whether two sequents can be unified
seqUnify s1 s2 = case check of
                     Left _ -> False
                     Right [] -> False
                     Right _ -> True
            where check = do fosub <- fosolve [rhs s1 :=: rhs s2]
                             acuisolve [lhs (applySub fosub s1) :=: lhs (applySub fosub s2)]


-- TODO: remove the need for this assumption.
-- | A simple check of whether one sequent unifies with a another, allowing
-- for weakening on the lhs; assumption is that neither side contains Delta -1
seqSubsetUnify s1 s2 = case check of
                       Left _ -> False
                       Right [] -> False
                       Right _ -> True
            where check = do fosub <- fosolve [rhs s1 :=: rhs s2]
                             acuisolve [(lhs (applySub fosub s1) :+: GammaV (0 - 1)) :=: lhs (applySub fosub s2) ]

--------------------------------------------------------
--Logics
--------------------------------------------------------

data PropLogic = MP | MT | DNE | DNI | DD | AX | CP1 | CP2 | ID1 | ID2 | ID3 | ID4
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
                     , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID2 = [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                     , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID3 = [ GammaV 1  :|-: SS (SeqPhi 2) 
                     , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                     ]
    premisesOf ID4 = [ GammaV 1  :|-: SS (SeqPhi 2) 
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
    conclusionOf ID4 = GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)

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
                        "ID"  -> return [ID1,ID2,ID3,ID4]

parsePropProof :: String -> [Either ParseError (DeductionLine PropLogic PurePropLexicon (Form Bool))]
parsePropProof = toDeduction parsePropLogic prePurePropFormulaParser


--------------------------------------------------------
--Utility Functions
--------------------------------------------------------

reduceResult :: Int -> [Either (ProofErrorMessage lex) [b]] -> Either (ProofErrorMessage lex) b
reduceResult lineno xs = case rights xs of
                           [] -> Left $ NoUnify (concat $ map eqsOf xs) lineno
                           (r:x):rs -> Right r
    where eqsOf (Left (NoUnify eqs _)) = eqs

--Given a list of concrete rules and a list of (variable-free) premise sequents, and a (variable-free) 
--conclusion succeedent, return an error or a list of possible (variable-free) correct 
--conclusion sequents
seqFromNode :: (Inference r lex, MaybeMonadVar (ClassicalSequentOver lex) (State Int),
        MonadVar (ClassicalSequentOver lex) (State Int)) =>  
    Int -> [r] -> [ClassicalSequentOver lex Sequent] -> ClassicalSequentOver lex Succedent 
      -> [Either (ProofErrorMessage lex) [ClassicalSequentOver lex Sequent]]
seqFromNode lineno rules prems conc = do rrule <- rules
                                         rprems <- permutations (premisesOf rrule) 
                                         return $ oneRule rrule rprems
    where oneRule r rp = do if length rp /= length prems 
                                then Left $ GenericError "Wrong number of premises" lineno
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
        ProofTree r lex -> Either (ProofErrorMessage lex) (ClassicalSequentOver lex Sequent)
reduceProofTree (Node (ProofLine no cont rule) ts) =  
        do prems <- mapM reduceProofTree ts
           reduceResult no $ seqFromNode no rule prems cont

fosolve :: (FirstOrder (ClassicalSequentOver lex), MonadVar (ClassicalSequentOver lex) (State Int)) =>  
    [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [Equation (ClassicalSequentOver lex)]
fosolve eqs = case evalState (foUnifySys (const False) eqs) (0 :: Int) of 
                [] -> Left $ NoUnify [eqs] 0
                [s] -> Right s

acuisolve :: (ACUI (ClassicalSequentOver lex), MonadVar (ClassicalSequentOver lex) (State Int)) =>  
    [Equation (ClassicalSequentOver lex)] -> Either (ProofErrorMessage lex) [[Equation (ClassicalSequentOver lex)]]
acuisolve eqs = 
        case evalState (acuiUnifySys (const False) eqs) (0 :: Int) of
          [] -> Left $ NoUnify [eqs] 0
          subs -> Right subs

rhs :: ClassicalSequentOver lex Sequent -> ClassicalSequentOver lex Succedent
rhs (x :|-: (Bot :-: y)) = rhs (x :|-: y)
rhs (_ :|-: y) = y 

lhs :: ClassicalSequentOver lex Sequent -> ClassicalSequentOver lex Antecedent
lhs (x :|-: _) = x
