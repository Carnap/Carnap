{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.Arithmetic.Parser ( arithmeticParser, arithmeticExtendedParser ) 
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
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

arithmeticExtendedOptions :: FirstOrderParserOptions ExtendedArithLex u Identity
arithmeticExtendedOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (lessThanParser x)
                                                        <|> try (equalsParser x)
                                                        <|> try (inequalityParser x)
                                                        <|> parsePredicateString x
                         , quantifiedSentenceParser' = lplQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "stuvwxyz"
                         , constantParser = Just (parseZero <|> parseConstant "abcdefghijklmnopqr")
                         , functionParser = Just (\x -> arithmeticOpParser 
                                                            (parenParser x
                                                            <|> parseZero 
                                                            <|> try (parseFunctionString x)
                                                            <|> parseFreeVar "stuvwxyz"
                                                            <|> parseConstant "abcdefghijklmnopqr"
                                                            ))
                         , hasBooleanConstants = True
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }
 

arithmeticParser = parserFromOptions arithmeticOptions <* eof

arithmeticExtendedParser = parserFromOptions arithmeticExtendedOptions <* eof

instance ParsableLex (Form Bool) ArithLex where
        langParser = arithmeticParser

instance ParsableLex (Form Bool) ExtendedArithLex where
        langParser = arithmeticExtendedParser

arithmeticOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [Postfix (try (iteratedParse parseSucc))]
                    , [Infix (try parsePlus) AssocLeft, Infix (try parseTimes) AssocLeft]
                    ]
