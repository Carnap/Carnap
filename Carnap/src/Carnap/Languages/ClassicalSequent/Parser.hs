{-#LANGUAGE TypeOperators, FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Carnap.Languages.ClassicalSequent.Parser (
    propSeqParser
) where

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

--XXX: need to add variable parsing
seqFormulaParser :: (Sequentable f, ParsableLex (Form Bool) f) =>
    Parsec String u (ClassicalSequentOver (f :|: EndLang) Sequent)
seqFormulaParser = do (lhs,rhs) <- splitSequent --split on turnstile and commas
                      let lhs'  = map (SA . liftToSequent) lhs
                      let rhs'  = map (SS . liftToSequent) rhs
                      let lhs'' = foldl (:+:) Top lhs'
                      let rhs'' = foldl (:-:) Bot rhs'
                      return $ lhs'' :|-: rhs''

splitSequent :: (ParsableLex (Form Bool) f) =>
    Parsec String u ([FixLang f (Form Bool)], [FixLang f (Form Bool)])
splitSequent = do lhs <- formlist
                  string ":|-:" <|> string "⊢"
                  rhs <- formlist
                  eof
                  return (lhs,rhs)

formlist :: (ParsableLex (Form Bool) f) =>
    Parsec String u [FixLang f (Form Bool)]
formlist = do spaces
              sepEndBy (try langParser) comma
    where comma = do spaces
                     char ','
                     spaces

--------------------------------------------------------
--2. Parsable Languages
--------------------------------------------------------

instance ParsableLex (Form Bool) PurePropLexicon where
        langParser = prePurePropFormulaParser

propSeqParser = seqFormulaParser :: Parsec String u (PropSequentCalc Sequent)
