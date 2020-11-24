{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.Hilbert (toProofTreeHilbert, toProofTreeHilbertImplicit, toDeductionHilbert, toDeductionHilbertImplicit)
where

import Data.Tree
import Data.Typeable
import Text.Parsec
import Carnap.Core.Data.Types
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser

parseAssertLineHilbert :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseAssertLineHilbert r f = do phi <- f
                                (rule,deps) <- rline r
                                return $ AssertLine phi rule 0 (map (\x -> (x,x)) deps)

parseAssertLineHilbertImplicit :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseAssertLineHilbertImplicit r f = do phi <- f
                                        rule <- spaces *> char ':' *> r 
                                        return $ AssertLine phi rule 0 []

toDeductionHilbert :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionHilbert r f = toDeduction (parseAssertLineHilbert r f)

toDeductionHilbertImplicit :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionHilbertImplicit r f = toDeduction (parseAssertLineHilbertImplicit r f)

toProofTreeHilbert :: 
    ( Inference r lex sem
    , Sequentable lex
    , Typeable sem
    ) => Deduction r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeHilbert ded n = case ded !! (n - 1)  of
      AssertLine f r@(r':_) dpth deps ->
            do mapM_ checkDep deps
               deps' <- mapM (toProofTreeHilbert ded) (map snd deps)
               return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
      PartialLine _ e _ -> Left $ NoParse e n
      where err x = Left $ GenericError x n
            takeRange m' n' | n' <= m' = err "Dependency is later than assertion"
                            | otherwise = Right ()
            lineRange m n = drop (m - 1) $ take n ded
            checkDep (begin,end) = takeRange end n

toProofTreeHilbertImplicit :: 
    ( Inference r lex sem
    , Sequentable lex
    , Typeable sem
    ) => Deduction r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeHilbertImplicit ded n = case ded !! (n - 1)  of
      AssertLine f r@(r':_) dpth _ -> 
            do dp <- case () of
                         _ | isAssumption r' || isPremise r' -> return []
                           | n == 1 -> err "proof must begin with a premise or assumption"
                           | otherwise -> return [n - 1]
               deps' <- mapM (toProofTreeHilbertImplicit ded) dp
               return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
      PartialLine _ e _ -> Left $ NoParse e n
      where err x = Left $ GenericError x n
            takeRange m' n' | n' <= m' = err "Dependency is later than assertion"
                            | otherwise = Right $ ()
