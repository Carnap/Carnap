module Carnap.Languages.PurePropositional.Parser (purePropFormulaParser, standardLetters, extendedLetters, PurePropositionalParserOptions(..)) where

import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Util (isBooleanBinary)
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

data PurePropositionalParserOptions u m = PurePropositionalParserOptions 
                                        { atomicSentenceParser :: ParsecT String u m PureForm 
                                        , hasBooleanConstants :: Bool
                                        , opTable :: [[Operator String u m PureForm]]
                                        , parenParsers :: [ParsecT String u m PureForm -> ParsecT String u m PureForm] 
                                        --an infinite stream of parsers for parenthesized formulas that we cycle 
                                        --through as we recur on parsing
                                        }

standardLetters :: Monad m => PurePropositionalParserOptions u m
standardLetters = PurePropositionalParserOptions 
                        { atomicSentenceParser = sentenceLetterParser "PQRSTUVW" 
                        , hasBooleanConstants = False
                        , opTable = standardOpTable
                        , parenParsers = repeat (\x -> parenParser x <* spaces)
                        }

extendedLetters :: Monad m => PurePropositionalParserOptions u m
extendedLetters = standardLetters { atomicSentenceParser = sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" }

--this parses as much formula as it can, but is happy to return an output if the
--initial segment of a string is a formula
purePropFormulaParser :: Monad m => PurePropositionalParserOptions u m -> ParsecT String u m PureForm
purePropFormulaParser opts = buildExpressionParser (opTable opts) subFormulaParser
    --subformulas are either
    where subFormulaParser = head (parenParsers opts) recur  --formulas wrapped in parentheses
                          <|> unaryOpParser [parseNeg] subFormulaParser --negations or modalizations of subformulas
                          <|> try (atomicSentenceParser opts <* spaces)--or atoms
                          <|> if hasBooleanConstants opts then try (booleanConstParser <* spaces) else parserZero
                          <|> ((schemevarParser <* spaces) <?> "")
          checkBinary a = if isBooleanBinary a then return a else unexpected "non-binary sentence wrapped in parentheses"
          recur = purePropFormulaParser $ opts {parenParsers = tail (parenParsers opts)}

standardOpTable :: Monad m => [[Operator String u m PureForm]]
standardOpTable = [ [ Prefix (try parseNeg)]
                  , [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft]
                  , [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]
                  ]
