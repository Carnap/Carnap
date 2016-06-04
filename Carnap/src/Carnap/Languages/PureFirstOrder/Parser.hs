module Carnap.Languages.PureFirstOrder.Parser (
folFormulaParser
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

folFormulaParser :: Parsec String () (PurePFOLForm EndLang)
folFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = parenParser folFormulaParser
                          <|> try (quantifiedSentenceParser 
                                        parseFreeVar folFormulaParser)
                          <|> unaryOpParser [parseNeg] subFormulaParser
                          <|> try (molecularSentenceParser parseTerm)

parseFreeVar :: Parsec String () (PurePFOLTerm a)
parseFreeVar = choice [try $ do _ <- string "x_"
                                dig <- many1 digit
                                return $ PV $ "x_" ++ dig
                      ,      do c <- oneOf "xyzw"
                                return $ PV [c]
                      ]

parseConstant :: Parsec String () (PurePFOLTerm a)
parseConstant = do _ <- string "c_"
                   n <- number
                   return $ PC n
    where number = do { ds <- many1 digit; return (read ds) } <?> "number"

parseTerm :: Parsec String () (PurePFOLTerm EndLang)
parseTerm = try parseConstant <|> parseFreeVar

opTable :: Monad m => [[Operator String u m (PurePFOLForm a)]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
