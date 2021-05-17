{-#LANGUAGE TypeOperators, ScopedTypeVariables, FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Carnap.Languages.ClassicalSequent.Parser (ParsableLex(..), parseSeqOver, seqFormulaParser) where

import Text.Parsec
import Data.Typeable
import Carnap.Core.Data.Types
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses


--------------------------------------------------------
--1. The parser
--------------------------------------------------------

seqFormulaParser :: (Sequentable f, ParsableLex sem f, Typeable sem) => 
    Parsec String u (ClassicalSequentOver f (Sequent sem))
seqFormulaParser = parseSeqOver langParser 

--XXX: need to add variable parsing
parseSeqOver :: (Sequentable f, Typeable sem) => Parsec String u (FixLang f sem) -> 
    Parsec String u (ClassicalSequentOver f (Sequent sem))
parseSeqOver parser = do (lhs,rhs) <- splitSequent parser 
                         --split on turnstile and commas
                         let lhs'  = map liftL lhs
                         let rhs' = map liftR rhs
                         let lhs'' = case lhs' of
                               [] -> Top
                               x:xs -> foldl (:+:) x xs
                         let rhs'' = case rhs' of
                               [] -> Bot
                               x:xs -> foldl (:-:) x xs
                         return $ lhs'' :|-: rhs''
        where liftL :: (Typeable sem, Sequentable f) => FixLang f sem -> ClassicalSequentOver f (Antecedent sem)
              liftL x = SA (liftToSequent x)
              liftR :: (Typeable sem, Sequentable f) => FixLang f sem -> ClassicalSequentOver f (Succedent sem)
              liftR x = SS (liftToSequent x)

splitSequent :: Parsec String u (FixLang f sem) -> 
    Parsec String u ([FixLang f sem], [FixLang f sem])
splitSequent parser = do lhs <- formlist parser
                         string ":|-:" <|> string "⊢"
                         rhs <- formlist parser
                         return (lhs,rhs)

formlist :: Parsec String u (FixLang f sem) -> 
    Parsec String u [FixLang f sem]
formlist parser = try (spaces *> string "⊤" *> spaces *> return []) <|> (spaces *> sepEndBy (try parser) comma)
    where comma = do spaces
                     char ','
                     spaces

