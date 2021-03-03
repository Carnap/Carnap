{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.HigherOrderArithmetic.Parser ( untypedHigherOrderArithmeticParser) where

import Carnap.Core.Data.Types
import Carnap.Languages.HigherOrderArithmetic.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.ClassicalSequent.Parser
import Control.Monad.Identity
import Carnap.Languages.PureFirstOrder.Parser (FirstOrderParserOptions(..), parserFromOptions, parseFreeVar)
import Carnap.Languages.PurePropositional.Parser (standardOpTable)
import Text.Parsec
import Text.Parsec.Expr

untypedHigherOrderArithmeticOptions :: FirstOrderParserOptions UntypedHigherOrderArithLex u Identity
untypedHigherOrderArithmeticOptions = FirstOrderParserOptions
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> try (lessThanParser x)
                                                          <|> try (inequalityParser x)
                                                          <|> subsetParser x
                                                          <|> parsePredicateString x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "stuvwxyz"
                           , constantParser = Just (parseConstant "abcdefghijklmnopqr" <|> try parseEmptySet 
                                                    <|> separationParser vparser tparser
                                                        (parserFromOptions untypedHigherOrderArithmeticOptions))
                           , functionParser = Just (\x -> untypedHigherOrderArithmeticOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> parseZero 
                                                                 <|> try parseEmptySet
                                                                 <|> try (parseFunctionString x)
                                                                 <|> vparser
                                                                 <|> cparser
                                                                 ))
                           , hasBooleanConstants = True
                           , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }
    where cparser = case constantParser untypedHigherOrderArithmeticOptions of Just c -> c
          fparser = case functionParser untypedHigherOrderArithmeticOptions of Just f -> f
          vparser = freeVarParser untypedHigherOrderArithmeticOptions 
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

untypedHigherOrderArithmeticParser = parserFromOptions untypedHigherOrderArithmeticOptions

instance ParsableLex (Form Bool) UntypedHigherOrderArithLex where
        langParser = untypedHigherOrderArithmeticParser

untypedHigherOrderArithmeticOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [Postfix (try (iteratedParse parseSucc))]
                    , [Infix (try parsePlus) AssocLeft, Infix (try parseTimes) AssocLeft]
                    , [Infix (try parseIntersect) AssocLeft, Infix (try parseUnion) AssocLeft]
                    , [Infix (try parseComplement) AssocNone]
                    ]
