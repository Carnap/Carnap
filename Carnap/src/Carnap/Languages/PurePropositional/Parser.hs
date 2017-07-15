module Carnap.Languages.PurePropositional.Parser (purePropFormulaParser, standardLetters, extendedLetters) where

import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

data PurePropositionalParserOptions u m = PurePropositionalParserOptions 
                                        { atomicSentenceParser :: ParsecT String u m PureForm 
                                        , hasBooleanConstants :: Bool}

standardLetters :: Monad m => PurePropositionalParserOptions u m
standardLetters = PurePropositionalParserOptions 
                        { atomicSentenceParser = sentenceLetterParser "PQRSTUVW" 
                        , hasBooleanConstants = False
                        }

extendedLetters :: Monad m => PurePropositionalParserOptions u m
extendedLetters = PurePropositionalParserOptions 
                        { atomicSentenceParser = sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 
                        , hasBooleanConstants = False
                        }

--this parses as much formula as it can, but is happy to return an output if the
--initial segment of a string is a formula
purePropFormulaParser :: Monad m => PurePropositionalParserOptions u m -> ParsecT String u m PureForm
purePropFormulaParser opts = buildExpressionParser opTable subFormulaParser
    --subformulas are either
    where subFormulaParser = (parenParser (purePropFormulaParser opts) <* spaces)  --formulas wrapped in parentheses
                          <|> unaryOpParser [parseNeg] subFormulaParser --negations or modalizations of subformulas
                          <|> try (atomicSentenceParser opts <* spaces)--or atoms
                          <|> if hasBooleanConstants opts then try (booleanConstParser <* spaces) else parserZero
                          <|> (schemevarParser <* spaces)

opTable :: Monad m => [[Operator String u m PureForm]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
