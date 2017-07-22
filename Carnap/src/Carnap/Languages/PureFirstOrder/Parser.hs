{-#LANGUAGE TypeOperators, FlexibleContexts#-}
module Carnap.Languages.PureFirstOrder.Parser ( folFormulaParser, mfolFormulaParser, magnusFOLFormulaParser ) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses (Schematizable)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage(..), QuantLanguage(..))
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
                         }

simplePolyadicFOLParserOptions :: PureFirstOrderParserOptions PureLexiconPFOL u Identity
simplePolyadicFOLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (parsePredicateSymbol "FGHIJKLMNO" x)
                                                        <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         }

simpleMonadicFOLParserOptions :: PureFirstOrderParserOptions PureLexiconMFOL u Identity
simpleMonadicFOLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> try (monadicSentenceParser x) <|> sentenceLetterParser "PQRSTUVW"
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "vwxyz"
                         , constantParser = Just (parseConstant "abcde")
                         , functionParser = Nothing
                         }

magnusFOLParserOptions :: PureFirstOrderParserOptions PureLexiconFOL u Identity
magnusFOLParserOptions = PureFirstOrderParserOptions 
                         { atomicSentenceParser = \x -> parsePredicateSymbolNoParen "ABCDEFGHIJKLMNOPQRSTUVWXYZ" x
                                                        <|> equalsParser x 
                         , quantifiedSentenceParser' = quantifiedSentenceParser
                         , freeVarParser = parseFreeVar "xyz"
                         , constantParser = Just (parseConstant "abcdefghijklmnopqrstuvw")
                         , functionParser = Nothing
                         }

rawFOLFormulaParser :: ( Monad m, Schematizable (a (PureFirstOrderLanguageWith a))
                       , MaybeStaticVar (a (PureFirstOrderLanguageWith a))
                       , FirstOrderLex (a (PureFirstOrderLanguageWith a))) =>
    PureFirstOrderParserOptions (CoreLexicon :|: a) u m -> ParsecT String u m (PureFirstOrderLanguageWith a (Form Bool))
rawFOLFormulaParser opts = buildExpressionParser opTable subFormulaParser
    where subFormulaParser = try (parenParser (rawFOLFormulaParser opts <* spaces))
                         <|> try (unaryOpParser [parseNeg] subFormulaParser)
                         <|> try (quantifiedSentenceParser vparser subFormulaParser <* spaces)
                         <|> (atomicSentenceParser opts tparser <* spaces)
          --Constants, if there are any
          cparser = case constantParser opts of Just c -> c
                                                Nothing -> mzero
          --Function symbols, if there are any
          fparser = case functionParser opts of Just f -> f
                                                Nothing -> const mzero
          --Free variables
          vparser = freeVarParser opts 
          --Terms
          tparser = try (fparser tparser) <|> cparser <|> vparser

magnusFOLFormulaParser :: Parsec String u PureFOLForm
magnusFOLFormulaParser = rawFOLFormulaParser magnusFOLParserOptions

folFormulaParser :: Parsec String u PureFOLForm
folFormulaParser = rawFOLFormulaParser standardFOLParserOptions

pfolFormulaParser :: Parsec String u PurePFOLForm
pfolFormulaParser = rawFOLFormulaParser simplePolyadicFOLParserOptions

mfolFormulaParser :: Parsec String u PureMFOLForm
mfolFormulaParser = rawFOLFormulaParser simpleMonadicFOLParserOptions

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

opTable :: Monad m => [[Operator String u m (PureFirstOrderLanguageWith a (Form Bool))]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
