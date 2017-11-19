{-#LANGUAGE TypeOperators, FlexibleContexts#-}
module Carnap.Languages.PureFirstOrder.Parser ( folFormulaParser, mfolFormulaParser, magnusFOLFormulaParser, thomasBolducAndZachFOLFormulaParser, hardegreePLFormulaParser) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses (Schematizable)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, BooleanConstLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Control.Monad.Identity

data PureFirstOrderParserOptions lex u m = PureFirstOrderParserOptions 
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

standardFOLParserOptions :: PureFirstOrderParserOptions PureLexiconFOL u Identity
standardFOLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbol "FGHIJKLMNO" x
                                                        <|> sentenceLetterParser "PQRSTUVW"
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Just (parseFunctionSymbol "fgh")
                         , hasBooleanConstants = False
                         }

simplePolyadicFOLParserOptions :: PureFirstOrderParserOptions PureLexiconPFOL u Identity
simplePolyadicFOLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbol "FGHIJKLMNO" x)
                                                        <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

simpleMonadicFOLParserOptions :: PureFirstOrderParserOptions PureLexiconMFOL u Identity
simpleMonadicFOLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (monadicSentenceParser x) <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

magnusFOLParserOptions :: PureFirstOrderParserOptions PureLexiconFOL u Identity
magnusFOLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvw")
                         , functionParser = Nothing
                         , hasBooleanConstants = False
                         }

thomasBolducAndZachFOLParserOptions :: PureFirstOrderParserOptions PureLexiconFOL u Identity
thomasBolducAndZachFOLParserOptions = magnusFOLParserOptions { hasBooleanConstants = True }

hardegreeSLParserOptions :: PureFirstOrderParserOptions PureLexiconFOL u Identity
hardegreeSLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "tuvwxyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrs")
                         , functionParser = Nothing
                         , hasBooleanConstants = True
                         }

coreSubformulaParser :: ( BoundVars lex
                        , BooleanLanguage (FixLang lex (Form Bool))
                        , BooleanConstLanguage (FixLang lex (Form Bool))
                        , QuantLanguage (FixLang lex (Form Bool)) (FixLang lex (Term Int))
                        ) =>
    Parsec String u (FixLang lex (Form Bool)) -> PureFirstOrderParserOptions lex u Identity
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
          tparser = try (fparser tparser) <|> cparser <|> vparser

parserFromOptions opts = buildExpressionParser opTable subformulaParser
    where subformulaParser = coreSubformulaParser (parserFromOptions opts) opts 

magnusFOLFormulaParser :: Parsec String u PureFOLForm
magnusFOLFormulaParser = parserFromOptions magnusFOLParserOptions

thomasBolducAndZachFOLFormulaParser :: Parsec String u PureFOLForm
thomasBolducAndZachFOLFormulaParser = parserFromOptions thomasBolducAndZachFOLParserOptions

hardegreePLFormulaParser :: Parsec String u PureFOLForm
hardegreePLFormulaParser = parserFromOptions thomasBolducAndZachFOLParserOptions

folFormulaParser :: Parsec String u PureFOLForm
folFormulaParser = parserFromOptions standardFOLParserOptions

pfolFormulaParser :: Parsec String u PurePFOLForm
pfolFormulaParser = parserFromOptions simplePolyadicFOLParserOptions

mfolFormulaParser :: Parsec String u PureMFOLForm
mfolFormulaParser = parserFromOptions simpleMonadicFOLParserOptions

parseFreeVar :: String -> Parsec String u (PureFirstOrderLanguageWith a (Term Int))
parseFreeVar s = choice [try $ do _ <- string "x_"
                                  dig <- many1 digit
                                  return $ PV $ "x_" ++ dig
                        ,      do c <- oneOf s
                                  return $ PV [c]
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
