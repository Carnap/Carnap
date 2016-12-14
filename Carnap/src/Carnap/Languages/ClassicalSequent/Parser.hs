{-#LANGUAGE TypeOperators, ScopedTypeVariables, FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Carnap.Languages.ClassicalSequent.Parser (ParsableLex(..), seqFormulaParser) where

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
    Parsec String u (ClassicalSequentOver f Sequent)
seqFormulaParser = do (lhs,rhs) <- splitSequent --split on turnstile and commas
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
