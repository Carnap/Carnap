{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.Arithmetic.Parser ( arithmeticParser, arithmeticExtendedParser, arithmeticExtendedSchemaParser) 
where

import Carnap.Core.Data.Types
import Carnap.Languages.Arithmetic.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.ClassicalSequent.Parser
import Control.Monad.Identity
import Carnap.Languages.PureFirstOrder.Parser (FirstOrderParserOptions(..), parserFromOptions, parseFreeVar)
import Carnap.Languages.PurePropositional.Parser (standardOpTable)
import Text.Parsec
import Text.Parsec.Expr

extendedSymbols = ['_','>','#']

arithmeticOptions :: FirstOrderParserOptions ArithLex u Identity
arithmeticOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (lessThanParser x)
                                                        <|> try (equalsParser x)
                                                        <|> inequalityParser x
                         , quantifiedSentenceParser' = lplQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "stuvwxyz"
                         , constantParser = Just (parseZero <|> parseConstant "abcdefghijklmnopqr")
                         , functionParser = Just (\x -> arithmeticOpParser 
                                                            (parenParser x
                                                            <|> parseZero 
                                                            <|> parseFreeVar "stuvwxyz"
                                                            <|> parseConstant "abcdefghijklmnopqr"
                                                            ))
                         , hasBooleanConstants = True
                         , parenRecur = parenOrBracket
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }
    where parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

arithmeticExtendedOptions :: FirstOrderParserOptions ExtendedArithLex u Identity
arithmeticExtendedOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (lessThanParser x)
                                                        <|> try (equalsParser x)
                                                        <|> try (inequalityParser x)
                                                        <|> parsePredicateString extendedSymbols x
                         , quantifiedSentenceParser' = lplQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "stuvwxyz"
                         , constantParser = Just (parseZero <|> parseConstant "abcdefghijklmnopqr")
                         , functionParser = Just (\x -> arithmeticOpParser 
                                                            (parenParser x
                                                            <|> parseZero 
                                                            <|> try (parseFunctionString extendedSymbols x)
                                                            <|> parseFreeVar "stuvwxyz"
                                                            <|> parseConstant "abcdefghijklmnopqr"
                                                            ))
                         , hasBooleanConstants = True
                         , parenRecur = parenOrBracket
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }
    where parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

arithmeticExtendedSchemaOptions :: FirstOrderParserOptions ExtendedArithLex u Identity
arithmeticExtendedSchemaOptions = arithmeticExtendedOptions 
                         { atomicSentenceParser = \x -> try (lessThanParser x)
                                                        <|> try (equalsParser x)
                                                        <|> try (inequalityParser x)
                                                        <|> try (parseFriendlySchematicPredicateSymbol x)
                                                        <|> parsePredicateString extendedSymbols x
                         , constantParser = Just $ parseZero 
                                               <|> try (parseFriendlySchematicConstant)
                                               <|> parseConstant "abcdefghijklmnopqr"
                         , functionParser = Just (\x -> arithmeticOpParser 
                                                            (parenParser x
                                                            <|> parseZero 
                                                            <|> try (parseFunctionString extendedSymbols x)
                                                            <|> try (parseFriendlySchematicFunctionSymbol x)
                                                            <|> try (parseFriendlySchematicConstant)
                                                            <|> parseFreeVar "stuvwxyz"
                                                            <|> parseConstant "abcdefghijklmnopqr"
                                                            ))
                         }

arithmeticParser = parserFromOptions arithmeticOptions

arithmeticExtendedParser = parserFromOptions arithmeticExtendedOptions

arithmeticExtendedSchemaParser = parserFromOptions arithmeticExtendedSchemaOptions

instance ParsableLex (Form Bool) ArithLex where
        langParser = arithmeticParser

instance ParsableLex (Form Bool) ExtendedArithLex where
        langParser = arithmeticExtendedParser

arithmeticOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [Postfix (try (iteratedParse parseSucc))]
                    , [Infix (try parsePlus) AssocLeft, Infix (try parseTimes) AssocLeft]
                    ]
