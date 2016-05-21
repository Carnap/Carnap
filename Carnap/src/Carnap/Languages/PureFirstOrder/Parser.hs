module Carnap.Languages.PureFirstOrder.Parser (
folFormulaParser
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage, QuantLanguage(..), PolyadicPredicateLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

folFormulaParser :: Parsec String () PureFOLForm
folFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = parenParser folFormulaParser
                      <|> try quantifierParser
                      <|> unaryOpParser [parseNeg] subFormulaParser
                      <|> try atomParser

opTable :: Monad m => [[Operator String u m PureFOLForm]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

quantifierParser :: Parsec String () PureFOLForm
quantifierParser = do s <- oneOf "AE∀∃"
                      v@(PV v') <- parseFreeVar
                      f <- folFormulaParser
                      let bf = \x -> subBoundVar v x f 
                          --partially applied, returning a function
                      return $ if s `elem` "A∀" then lall v' bf else lsome v' bf 
                          --which we bind

parseFreeVar :: Parsec String () PureFOLTerm
parseFreeVar = choice [try $ do _ <- string "x_"
                                dig <- many1 digit
                                return $ PV $ "x_" ++ dig
                      ,      do c <- oneOf "xyzw"
                                return $ PV [c]
                      ]

parseConstant :: Parsec String () PureFOLTerm
parseConstant = do _ <- string "x_"
                   n <- number
                   return $ PC n
    where number = do { ds <- many1 digit; return (read ds) } <?> "number"

parseTerm :: Parsec String () PureFOLTerm
parseTerm = try parseConstant <|> parseFreeVar

