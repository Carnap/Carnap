{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Parser 
( strictSetTheoryParser, strictSetTheoryMontagueParser
, extendedStrictSetTheoryParser, extendedStrictSetTheorySchemaParser, extendedStrictSetTheoryMontagueParser
, elementarySetTheoryParser, elementarySetTheoryMontagueParser
, extendedElementarySetTheoryParser, extendedElementarySetTheorySchemaParser, extendedElementarySetTheoryMontagueParser
, separativeSetTheoryParser, separativeSetTheoryMontagueParser
, extendedSeparativeSetTheoryParser, extendedSeparativeSetTheorySchemaParser, extendedSeparativeSetTheoryMontagueParser
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

extendedSymbols = ['_','>','#']

strictSetTheoryOptions :: FirstOrderParserOptions StrictSetTheoryLex u Identity
strictSetTheoryOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (elementParser x)
                                                        <|> try (equalsParser x)
                                                        <|> inequalityParser x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "stuvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqr")
                         , functionParser = Nothing
                         , hasBooleanConstants = True
                         , parenRecur = parenOrBracket
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }
    where parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

strictSetTheoryParser = parserFromOptions strictSetTheoryOptions

strictSetTheoryMontagueParser = parserFromOptions strictSetTheoryOptions {hasBooleanConstants = False}

instance ParsableLex (Form Bool) StrictSetTheoryLex where
        langParser = strictSetTheoryParser

extendedStrictSetTheoryOptions :: FirstOrderParserOptions ExtendedStrictSetTheoryLex u Identity
extendedStrictSetTheoryOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (elementParser x)
                                                    <|> try (equalsParser x)
                                                    <|> inequalityParser x
                                                    <|> parsePredicateString extendedSymbols x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "stuvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqr")
                         , functionParser = Just (parseFunctionString extendedSymbols)
                         , hasBooleanConstants = True
                         , parenRecur = parenOrBracket
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }
    where parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

extendedStrictSetTheorySchemaOptions :: FirstOrderParserOptions ExtendedStrictSetTheoryLex u Identity
extendedStrictSetTheorySchemaOptions = extendedStrictSetTheoryOptions 
                         { atomicSentenceParser = \x -> try (elementParser x)
                                                    <|> try (equalsParser x)
                                                    <|> inequalityParser x
                                                    <|> try (parseFriendlySchematicPredicateSymbol x)
                                                    <|> parsePredicateString extendedSymbols x
                         , constantParser = Just ( try (parseFriendlySchematicConstant)
                                               <|> parseConstant "abcdefghijklmnopqr")
                         , functionParser = Just $ \x -> try (parseFunctionString extendedSymbols x) 
                                                     <|> parseFriendlySchematicFunctionSymbol x
                         }

extendedStrictSetTheoryParser = parserFromOptions extendedStrictSetTheoryOptions

extendedStrictSetTheoryMontagueParser = parserFromOptions extendedStrictSetTheoryOptions {hasBooleanConstants = False}

extendedStrictSetTheorySchemaParser = parserFromOptions extendedStrictSetTheorySchemaOptions

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
                           , parenRecur = parenOrBracket
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }
    where parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

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
                                                      <|> parsePredicateString extendedSymbols x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "stuvwxyz"
                           , constantParser = Just (try parseEmptySet <|> parseConstant "abcdefghijklmnopqr" )
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> try parseEmptySet
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

extendedElementarySetTheorySchemaOptions :: FirstOrderParserOptions ExtendedElementarySetTheoryLex u Identity
extendedElementarySetTheorySchemaOptions = extendedElementarySetTheoryOptions 
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> try (inequalityParser x)
                                                          <|> try (parseFriendlySchematicPredicateSymbol x)
                                                          <|> subsetParser x
                                                          <|> parsePredicateString extendedSymbols x
                           , constantParser = Just $ try parseEmptySet 
                                                 <|> try (parseFriendlySchematicConstant)
                                                 <|> parseConstant "abcdefghijklmnopqr"
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> try parseEmptySet
                                                                 <|> try (parseFunctionString extendedSymbols x)
                                                                 <|> try (parseFriendlySchematicFunctionSymbol x)
                                                                 <|> try (parseFriendlySchematicConstant)
                                                                 <|> parseFreeVar "stuvwxyz" 
                                                                 <|> parseConstant "abcdefghijklmnopqr" 
                                                                 ))
                           }

extendedElementarySetTheoryParser = parserFromOptions extendedElementarySetTheoryOptions

extendedElementarySetTheoryMontagueParser = parserFromOptions extendedElementarySetTheoryOptions {hasBooleanConstants = False}

extendedElementarySetTheorySchemaParser = parserFromOptions extendedElementarySetTheorySchemaOptions

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
                           , parenRecur = parenOrBracket
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }
    where cparser = case constantParser separativeSetTheoryOptions of Just c -> c
          fparser = case functionParser separativeSetTheoryOptions of Just f -> f
          vparser = freeVarParser  separativeSetTheoryOptions 
          tparser = try (fparser tparser) <|> try cparser <|> vparser 
          parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

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
                                                          <|> parsePredicateString extendedSymbols x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "stuvwxyz"
                           , constantParser = Just $ parseConstant "abcdefghijklmnopqr" 
                                                 <|> try parseEmptySet 
                                                 <|> separationParser vparser tparser (parserFromOptions extendedSeparativeSetTheoryOptions)
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> try parseEmptySet
                                                                 <|> try (parseFunctionString extendedSymbols x)
                                                                 <|> vparser
                                                                 <|> cparser
                                                                 ))
                           , hasBooleanConstants = True
                           , parenRecur = parenOrBracket
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }
    where cparser = case constantParser extendedSeparativeSetTheoryOptions of Just c -> c
          fparser = case functionParser extendedSeparativeSetTheoryOptions of Just f -> f
          vparser = freeVarParser  extendedSeparativeSetTheoryOptions 
          tparser = try (fparser tparser) <|> try cparser <|> vparser 
          parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

extendedSeparativeSetTheorySchemaOptions :: FirstOrderParserOptions ExtendedSeparativeSetTheoryLex u Identity
extendedSeparativeSetTheorySchemaOptions = extendedSeparativeSetTheoryOptions
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> try (inequalityParser x)
                                                          <|> subsetParser x
                                                          <|> try (parseFriendlySchematicPredicateSymbol x)
                                                          <|> parsePredicateString extendedSymbols x
                           , constantParser = Just $ parseConstant "abcdefghijklmnopqr" 
                                                 <|> try parseEmptySet 
                                                 <|> try (parseFriendlySchematicConstant)
                                                 <|> separationParser vparser tparser (parserFromOptions extendedSeparativeSetTheoryOptions)
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> try parseEmptySet
                                                                 <|> try (parseFunctionString extendedSymbols x)
                                                                 <|> try (parseFriendlySchematicFunctionSymbol x)
                                                                 <|> try (parseFriendlySchematicConstant)
                                                                 <|> vparser
                                                                 <|> cparser
                                                                 ))
                           }
    where cparser = case constantParser extendedSeparativeSetTheorySchemaOptions of Just c -> c
          fparser = case functionParser extendedSeparativeSetTheorySchemaOptions of Just f -> f
          vparser = freeVarParser extendedSeparativeSetTheorySchemaOptions 
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

extendedSeparativeSetTheoryParser = parserFromOptions extendedSeparativeSetTheoryOptions

extendedSeparativeSetTheoryMontagueParser = parserFromOptions extendedSeparativeSetTheoryOptions {hasBooleanConstants = False}

extendedSeparativeSetTheorySchemaParser = parserFromOptions extendedSeparativeSetTheorySchemaOptions

instance ParsableLex (Form Bool) ExtendedSeparativeSetTheoryLex where
        langParser = extendedSeparativeSetTheoryParser

setTheoryOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [Infix (try parseIntersect) AssocLeft, Infix (try parseUnion) AssocLeft]
                    , [Infix (try parseComplement) AssocNone]
                    ]
