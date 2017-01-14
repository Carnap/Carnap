{-#LANGUAGE TypeOperators, ScopedTypeVariables, FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Carnap.Languages.ClassicalSequent.Parser (ParsableLex(..), parseSeqOver, seqFormulaParser) where

import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.ClassicalSequent.Syntax


--------------------------------------------------------
--1. The parser
--------------------------------------------------------

class ParsableLex a f where
        langParser :: Parsec String u (FixLang f a)
        

seqFormulaParser :: (Sequentable f, ParsableLex (Form Bool) f) => 
    Parsec String u (ClassicalSequentOver f Sequent)
seqFormulaParser = parseSeqOver langParser 

--XXX: need to add variable parsing
parseSeqOver :: (Sequentable f) => Parsec String u (FixLang f (Form Bool)) -> 
    Parsec String u (ClassicalSequentOver f Sequent)
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
        where liftL :: Sequentable f => FixLang f (Form Bool) -> ClassicalSequentOver f Antecedent
              liftL x = SA (liftToSequent x)
              liftR :: Sequentable f => FixLang f (Form Bool) -> ClassicalSequentOver f Succedent
              liftR x = SS (liftToSequent x)

splitSequent :: Parsec String u (FixLang f (Form Bool)) -> 
    Parsec String u ([FixLang f (Form Bool)], [FixLang f (Form Bool)])
splitSequent parser = do lhs <- formlist parser
                         string ":|-:" <|> string "⊢"
                         rhs <- formlist parser
                         eof
                         return (lhs,rhs)

formlist :: Parsec String u (FixLang f (Form Bool)) -> 
    Parsec String u [FixLang f (Form Bool)]
formlist parser = do spaces
                     sepEndBy (try parser) comma
    where comma = do spaces
                     char ','
                     spaces

