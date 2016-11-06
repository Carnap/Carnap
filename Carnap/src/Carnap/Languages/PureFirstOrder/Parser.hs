{-#LANGUAGE TypeOperators, FlexibleContexts#-}
module Carnap.Languages.PureFirstOrder.Parser (
folFormulaParser, mfolFormulaParser
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage(..), QuantLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

pfolFormulaParser :: Parsec String u PurePFOLForm
pfolFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = coreParser pfolFormulaParser subFormulaParser
                      <|> try (molecularSentenceParser parseSimpleFOLTerm)

folFormulaParser :: Parsec String u PureFOLForm
folFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = coreParser folFormulaParser subFormulaParser
                      <|> try (molecularSentenceParser parseComplexFOLTerm)
                      <|> try (equalsParser parseComplexFOLTerm) 

mfolFormulaParser :: Parsec String u PureMFOLForm
mfolFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = coreParser mfolFormulaParser subFormulaParser
                      <|> try monadicSentenceParser 

coreParser recur sfrecur = parenParser recur
      <|> try (quantifiedSentenceParser parseFreeVar sfrecur)
      <|> unaryOpParser [parseNeg] sfrecur

parseFreeVar :: Parsec String u (PureFirstOrderLanguageWith a (Term Int))
parseFreeVar = choice [try $ do _ <- string "x_"
                                dig <- many1 digit
                                return $ PV $ "x_" ++ dig
                      ,      do c <- oneOf "xyzw"
                                return $ PV [c]
                      ]

parseConstant :: Parsec String u (PureFirstOrderLanguageWith a (Term Int))
parseConstant = do _ <- string "c_"
                   n <- number
                   return $ PC n

monadicSentenceParser :: Parsec String u PureMFOLForm
monadicSentenceParser = do _ <- string "P_"
                           n <- number
                           _ <- char '('
                           t <- parseSimpleFOLTerm
                           _ <- char ')'
                           return (PMPred n :!$: t)

parseSimpleFOLTerm :: Parsec String u (PureFirstOrderLanguageWith a (Term Int))
parseSimpleFOLTerm = try parseConstant <|> parseFreeVar

parseComplexFOLTerm :: Parsec String u (PureLanguageFOL (Term Int)) 
parseComplexFOLTerm = try parseConstant 
                    <|> parseFreeVar
                    <|> molecularTermParser parseComplexFOLTerm

opTable :: Monad m => [[Operator String u m (PureFirstOrderLanguageWith a (Form Bool))]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
