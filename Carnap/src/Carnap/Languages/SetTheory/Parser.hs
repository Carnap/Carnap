{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Parser 
( strictSetTheoryParser, strictSetTheoryMontagueParser
, extendedStrictSetTheoryParser, extendedStrictSetTheoryMontagueParser
, elementarySetTheoryParser, elementarySetTheoryMontagueParser
, extendedElementarySetTheoryParser, extendedElementarySetTheoryMontagueParser
, separativeSetTheoryParser, separativeSetTheoryMontagueParser
, extendedSeparativeSetTheoryParser, extendedSeparativeSetTheoryMontagueParser
) where

import Carnap.Core.Data.Types
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.ClassicalSequent.Parser
import Control.Monad.Identity
import Carnap.Languages.PureFirstOrder.Parser (FirstOrderParserOptions(..), parserFromOptions, parseFreeVar)
import Carnap.Languages.PurePropositional.Parser (standardOpTable)
import Text.Parsec
import Text.Parsec.Expr

strictSetTheoryOptions :: FirstOrderParserOptions StrictSetTheoryLex u Identity
strictSetTheoryOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (elementParser x)
                                                        <|> try (equalsParser x)
                                                        <|> inequalityParser x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "stuvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqr")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

strictSetTheoryParser = parserFromOptions strictSetTheoryOptions

strictSetTheoryMontagueParser = parserFromOptions strictSetTheoryOptions {hasBooleanConstants = False}

instance ParsableLex (Form Bool) StrictSetTheoryLex where
        langParser = strictSetTheoryParser

extendedStrictSetTheoryOptions :: FirstOrderParserOptions ExtendedStrictSetTheoryLex u Identity
extendedStrictSetTheoryOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (elementParser x)
                                                        <|> try (equalsParser x)
                                                        <|> inequalityParser x
                                                        <|> parsePredicateString x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "stuvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqr")
                         , functionParser = Just parseFunctionString
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

extendedStrictSetTheoryParser = parserFromOptions extendedStrictSetTheoryOptions

extendedStrictSetTheoryMontagueParser = parserFromOptions extendedStrictSetTheoryOptions {hasBooleanConstants = False}

instance ParsableLex (Form Bool) ExtendedStrictSetTheoryLex where
        langParser = extendedStrictSetTheoryParser

elementarySetTheoryOptions :: FirstOrderParserOptions ElementarySetTheoryLex u Identity
elementarySetTheoryOptions = FirstOrderParserOptions 
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> try (inequalityParser x)
                                                          <|> subsetParser x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "stuvwxyz"
                           , constantParser = Just (try parseEmptySet <|> parseConstant "abcdefghijklmnopqr" )
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> try parseEmptySet
                                                                 <|> parseFreeVar "stuvwxyz" 
                                                                 <|> parseConstant "abcdefghijklmnopqr" 
                                                                 ))
                           , hasBooleanConstants = True
                           , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }

elementarySetTheoryParser = parserFromOptions elementarySetTheoryOptions

elementarySetTheoryMontagueParser = parserFromOptions elementarySetTheoryOptions {hasBooleanConstants = False}

instance ParsableLex (Form Bool) ElementarySetTheoryLex where
        langParser = elementarySetTheoryParser

extendedElementarySetTheoryOptions :: FirstOrderParserOptions ExtendedElementarySetTheoryLex u Identity
extendedElementarySetTheoryOptions = FirstOrderParserOptions 
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> try (inequalityParser x)
                                                          <|> subsetParser x
                                                          <|> parsePredicateString x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "stuvwxyz"
                           , constantParser = Just (try parseEmptySet <|> parseConstant "abcdefghijklmnopqr" )
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> try parseEmptySet
                                                                 <|> try (parseFunctionString x)
                                                                 <|> parseFreeVar "stuvwxyz" 
                                                                 <|> parseConstant "abcdefghijklmnopqr" 
                                                                 ))
                           , hasBooleanConstants = False
                           , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }

extendedElementarySetTheoryParser = parserFromOptions extendedElementarySetTheoryOptions

extendedElementarySetTheoryMontagueParser = parserFromOptions extendedElementarySetTheoryOptions {hasBooleanConstants = False}

instance ParsableLex (Form Bool) ExtendedElementarySetTheoryLex where
        langParser = extendedElementarySetTheoryParser

separativeSetTheoryOptions :: FirstOrderParserOptions SeparativeSetTheoryLex u Identity
separativeSetTheoryOptions = FirstOrderParserOptions
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> try (inequalityParser x)
                                                          <|> subsetParser x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "stuvwxyz"
                           , constantParser = Just (parseConstant "abcdefghijklmnopqr" <|> try parseEmptySet
                                                    <|> separationParser vparser tparser
                                                        (parserFromOptions separativeSetTheoryOptions))
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> vparser
                                                                 <|> cparser
                                                                 ))
                           , hasBooleanConstants = True
                           , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }
    where cparser = case constantParser separativeSetTheoryOptions of Just c -> c
          fparser = case functionParser separativeSetTheoryOptions of Just f -> f
          vparser = freeVarParser  separativeSetTheoryOptions 
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

separativeSetTheoryParser = parserFromOptions separativeSetTheoryOptions

separativeSetTheoryMontagueParser = parserFromOptions separativeSetTheoryOptions {hasBooleanConstants = False}

instance ParsableLex (Form Bool) SeparativeSetTheoryLex where
        langParser = separativeSetTheoryParser

extendedSeparativeSetTheoryOptions :: FirstOrderParserOptions ExtendedSeparativeSetTheoryLex u Identity
extendedSeparativeSetTheoryOptions = FirstOrderParserOptions
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> try (inequalityParser x)
                                                          <|> subsetParser x
                                                          <|> parsePredicateString x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "stuvwxyz"
                           , constantParser = Just (parseConstant "abcdefghijklmnopqr" <|> try parseEmptySet 
                                                    <|> separationParser vparser tparser
                                                        (parserFromOptions extendedSeparativeSetTheoryOptions))
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
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
    where cparser = case constantParser extendedSeparativeSetTheoryOptions of Just c -> c
          fparser = case functionParser extendedSeparativeSetTheoryOptions of Just f -> f
          vparser = freeVarParser  extendedSeparativeSetTheoryOptions 
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

extendedSeparativeSetTheoryParser = parserFromOptions extendedSeparativeSetTheoryOptions

extendedSeparativeSetTheoryMontagueParser = parserFromOptions extendedSeparativeSetTheoryOptions {hasBooleanConstants = False}

instance ParsableLex (Form Bool) ExtendedSeparativeSetTheoryLex where
        langParser = extendedSeparativeSetTheoryParser

setTheoryOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [Infix (try parseIntersect) AssocLeft, Infix (try parseUnion) AssocLeft]
                    , [Infix (try parseComplement) AssocNone]
                    ]
