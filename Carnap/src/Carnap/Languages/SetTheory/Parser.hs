{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Parser 
( strictSetTheoryParser, elementarySetTheoryParser, separativeSetTheoryParser) where

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
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                         , opTable = standardOpTable
                         , finalValidation = const (pure ())
                         }

strictSetTheoryParser = parserFromOptions strictSetTheoryOptions

instance ParsableLex (Form Bool) StrictSetTheoryLex where
        langParser = strictSetTheoryParser

elementarySetTheoryOptions :: FirstOrderParserOptions ElementarySetTheoryLex u Identity
elementarySetTheoryOptions = FirstOrderParserOptions 
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> subsetParser x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "vwxyz"
                           , constantParser = Just (parseConstant "abcde")
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> parseFreeVar "vwxyz" 
                                                                 <|> parseConstant "abcde" 
                                                                 ))
                           , hasBooleanConstants = False
                           , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }

elementarySetTheoryParser = parserFromOptions elementarySetTheoryOptions

instance ParsableLex (Form Bool) ElementarySetTheoryLex where
        langParser = elementarySetTheoryParser

separativeSetTheoryOptions :: FirstOrderParserOptions SeparativeSetTheoryLex u Identity
separativeSetTheoryOptions = FirstOrderParserOptions
                           { atomicSentenceParser = \x -> try (elementParser x)
                                                          <|> try (equalsParser x)
                                                          <|> subsetParser x
                           , quantifiedSentenceParser' = quantifiedSentenceParser
                           , freeVarParser = parseFreeVar "vwxyz"
                           , constantParser = Just (parseConstant "abcde" <|>
                                                   separationParser vparser tparser
                                                        (parserFromOptions separativeSetTheoryOptions))
                           , functionParser = Just (\x -> setTheoryOpParser 
                                                                (parenParser x
                                                                 <|> powersetParser x
                                                                 <|> vparser
                                                                 <|> cparser
                                                                 ))
                           , hasBooleanConstants = False
                           , parenRecur = \opt recurWith  -> parenParser (recurWith opt)
                           , opTable = standardOpTable
                           , finalValidation = const (pure ())
                           }
    where cparser = case constantParser separativeSetTheoryOptions of Just c -> c
          fparser = case functionParser separativeSetTheoryOptions of Just f -> f
          vparser = freeVarParser  separativeSetTheoryOptions 
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

separativeSetTheoryParser = parserFromOptions separativeSetTheoryOptions

instance ParsableLex (Form Bool) SeparativeSetTheoryLex where
        langParser = separativeSetTheoryParser

setTheoryOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [Infix (try parseIntersect) AssocLeft, Infix (try parseUnion) AssocLeft]
                    , [Infix (try parseComplement) AssocNone]
                    ]
