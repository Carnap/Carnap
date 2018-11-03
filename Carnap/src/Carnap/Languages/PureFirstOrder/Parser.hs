{-#LANGUAGE TypeOperators, FlexibleContexts#-}
module Carnap.Languages.PureFirstOrder.Parser 
( folFormulaParser, folFormulaParserRelaxed, mfolFormulaParser
, magnusFOLFormulaParser, thomasBolducAndZachFOLFormulaParser
, hardegreePLFormulaParser, bergmannMoorAndNelsonPDFormulaParser
, goldfarbNDFormulaParser, FirstOrderParserOptions(..)
, parserFromOptions, parseFreeVar) where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes (Schematizable)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, StandardVarLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Control.Monad.Identity

data FirstOrderParserOptions lex u m = FirstOrderParserOptions 
                                         { atomicSentenceParser :: ParsecT String u m (FixLang lex (Term Int)) 
                                            -> ParsecT String u m (FixLang lex (Form Bool))
                                         , quantifiedSentenceParser' :: ParsecT String u m (FixLang lex (Term Int)) 
                                            -> ParsecT String u m (FixLang lex (Form Bool))
                                            -> ParsecT String u m (FixLang lex (Form Bool))
                                         , freeVarParser  :: ParsecT String u m (FixLang lex (Term Int)) 
                                         , constantParser :: Maybe (ParsecT String u m (FixLang lex (Term Int)))
                                         , functionParser :: Maybe (ParsecT String u m (FixLang lex (Term Int)) 
                                            -> ParsecT String u m (FixLang lex (Term Int)))
                                         , hasBooleanConstants :: Bool
                                         }

standardFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
standardFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbol "FGHIJKLMNO" x
                                                        <|> sentenceLetterParser "PQRSTUVW"
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Just (parseFunctionSymbol "fgh")
                         , hasBooleanConstants = False
                         }

simplePolyadicFOLParserOptions :: FirstOrderParserOptions PureLexiconPFOL u Identity
simplePolyadicFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbol "FGHIJKLMNO" x)
                                                        <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

simpleMonadicFOLParserOptions :: FirstOrderParserOptions PureLexiconMFOL u Identity
simpleMonadicFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (monadicSentenceParser x) <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

magnusFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
magnusFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvw")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

thomasBolducAndZachFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
thomasBolducAndZachFOLParserOptions = magnusFOLParserOptions { hasBooleanConstants = True }

bergmannMoorAndNelsonFOLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
bergmannMoorAndNelsonFOLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x)
                                                        <|> sentenceLetterParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ" 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "wxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuv")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

hardegreePLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
hardegreePLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen ['A' .. 'Z'] x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar ['t' .. 'z']
                         , constantParser = Just (parseConstant ['a' .. 's'])
                         , functionParser = Nothing
                         , hasBooleanConstants = True
                         }

goldfarbNDParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
goldfarbNDParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen ['A' .. 'Z'] x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar ['a' .. 'z']
                         , constantParser = Nothing
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

coreSubformulaParser :: ( BoundVars lex
                        , BooleanLanguage (FixLang lex (Form Bool))
                        , BooleanConstLanguage (FixLang lex (Form Bool))
                        , QuantLanguage (FixLang lex (Form Bool)) (FixLang lex (Term Int))
                        ) =>
    Parsec String u (FixLang lex (Form Bool)) -> FirstOrderParserOptions lex u Identity
        -> Parsec String u (FixLang lex (Form Bool))
coreSubformulaParser fp opts = (parenParser fp <* spaces)
                             <|> try (unaryOpParser [parseNeg] (coreSubformulaParser fp opts))
                             <|> try ((quantifiedSentenceParser' opts) vparser (coreSubformulaParser fp opts) <* spaces)
                             <|> (atomicSentenceParser opts tparser <* spaces)
                             <|> if hasBooleanConstants opts then try (booleanConstParser <* spaces) else parserZero
    where cparser = case constantParser opts of Just c -> c
                                                Nothing -> mzero
          --Function symbols, if there are any
          fparser = case functionParser opts of Just f -> f
                                                Nothing -> const mzero
          --Free variables
          vparser = freeVarParser opts 
          --Terms
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

parserFromOptions opts = buildExpressionParser opTable subformulaParser
    where subformulaParser = coreSubformulaParser (parserFromOptions opts) opts 

magnusFOLFormulaParser :: Parsec String u PureFOLForm
magnusFOLFormulaParser = parserFromOptions magnusFOLParserOptions

thomasBolducAndZachFOLFormulaParser :: Parsec String u PureFOLForm
thomasBolducAndZachFOLFormulaParser = parserFromOptions thomasBolducAndZachFOLParserOptions

hardegreePLFormulaParser :: Parsec String u PureFOLForm
hardegreePLFormulaParser = parserFromOptions hardegreePLParserOptions

goldfarbNDFormulaParser:: Parsec String u PureFOLForm
goldfarbNDFormulaParser = parserFromOptions goldfarbNDParserOptions

bergmannMoorAndNelsonPDFormulaParser :: Parsec String u PureFOLForm
bergmannMoorAndNelsonPDFormulaParser = parserFromOptions bergmannMoorAndNelsonFOLParserOptions

folFormulaParser :: Parsec String u PureFOLForm
folFormulaParser = parserFromOptions standardFOLParserOptions

folFormulaParserRelaxed :: Parsec String u PureFOLForm
folFormulaParserRelaxed = parserFromOptions (standardFOLParserOptions 
    { atomicSentenceParser = \x -> (try (atomicSentenceParser standardFOLParserOptions x) <|> parsePredicateSymbolNoParen "FGHIJKLMNO" x) })

pfolFormulaParser :: Parsec String u PurePFOLForm
pfolFormulaParser = parserFromOptions simplePolyadicFOLParserOptions

mfolFormulaParser :: Parsec String u PureMFOLForm
mfolFormulaParser = parserFromOptions simpleMonadicFOLParserOptions

parseFreeVar :: StandardVarLanguage (PureFirstOrderLanguageWith a (Term Int)) => String -> Parsec String u (PureFirstOrderLanguageWith a (Term Int))
parseFreeVar s = choice [try $ do _ <- string "x_"
                                  dig <- many1 digit
                                  return $ foVar $ "x_" ++ dig
                        ,      do c <- oneOf s
                                  return $ foVar [c]
                        ]

monadicSentenceParser :: Parsec String u PureMFOLTerm -> Parsec String u PureMFOLForm
monadicSentenceParser parseTerm = do _ <- string "P_"
                                     n <- number
                                     _ <- char '('
                                     t <- parseTerm
                                     _ <- char ')'
                                     return (PMPred n :!$: t)

opTable :: (BooleanLanguage (PureFirstOrderLanguageWith a (Form Bool)), Monad m)
    => [[Operator String u m (PureFirstOrderLanguageWith a (Form Bool))]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
