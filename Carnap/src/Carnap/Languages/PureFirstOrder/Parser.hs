{-#LANGUAGE TypeOperators #-}
module Carnap.Languages.PureFirstOrder.Parser (
folFormulaParser
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

pfolFormulaParser :: Parsec String () (PurePFOLForm EndLang)
pfolFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = parenParser pfolFormulaParser
                          <|> try (quantifiedSentenceParser 
                                        parseFreeVar pfolFormulaParser)
                          <|> unaryOpParser [parseNeg] subFormulaParser
                          <|> try (molecularSentenceParser parsePFOLTerm)

folFormulaParser :: Parsec String () (PurePFOL_EQ_FSForm)
folFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = parenParser folFormulaParser
                          <|> try (quantifiedSentenceParser 
                                        parseFreeVar folFormulaParser)
                          <|> unaryOpParser [parseNeg] subFormulaParser
                          <|> try (molecularSentenceParser parsePFOL_EQ_FSTerm)
                          <|> try (equalsParser parsePFOL_EQ_FSTerm)

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

parsePFOLTerm :: Parsec String () (PurePFOLTerm EndLang)
parsePFOLTerm = try parseConstant <|> parseFreeVar

parsePFOL_EQ_FSTerm :: Parsec String () (PurePFOL_EQ_FSTerm)
parsePFOL_EQ_FSTerm = try parseConstant 
                    <|> parseFreeVar
                    <|> molecularTermParser parsePFOL_EQ_FSTerm

opTable :: Monad m => [[Operator String u m (PurePFOLForm a)]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
