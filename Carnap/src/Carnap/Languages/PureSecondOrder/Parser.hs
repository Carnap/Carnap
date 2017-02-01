{-#LANGUAGE TypeOperators, FlexibleContexts#-}


module Carnap.Languages.PureSecondOrder.Parser
        (msolFormulaParser)
    where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage(..), QuantLanguage(..), PolyadicPredicateLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Data.List (findIndex)

msolFormulaParser :: Parsec String u (MonadicallySOL (Form Bool))
msolFormulaParser = buildExpressionParser opTable subFormulaParser 
    
subFormulaParser = coreParser msolFormulaParser subFormulaParser
                      <|> try (predicationParser parseSimpleFOTerm)

coreParser recur sfrecur = (parenParser recur <* spaces)
      <|> try (quantifiedSentenceParser parseFreeVar sfrecur)
      <|> try (quantifiedSentenceParser parseMSOLVar sfrecur)
      <|> try (atomicSentenceParser "PQRSTUVW" <* spaces)
      <|> unaryOpParser [parseNeg] sfrecur

parseFreeVar :: Parsec String u (MonadicallySOL (Term Int))
parseFreeVar = choice [try $ do _ <- string "x_"
                                dig <- many1 digit
                                return $ SOV $ "x_" ++ dig
                      ,      do c <- oneOf "vwxyz"
                                return $ SOV [c]
                      ]

parseMSOLVar :: Parsec String u (MonadicallySOL (Form (Int -> Bool)))
parseMSOLVar = choice [try $ do _ <- string "X_"
                                dig <- many1 digit
                                return $ SOMVar $ "X_" ++ dig
                      ,      do c <- oneOf "XYZ"
                                return $ SOMVar [c]
                      ]

parseSimpleFOTerm :: Parsec String u (MonadicallySOL (Term Int))
parseSimpleFOTerm = try parseConstant <|> parseFreeVar

parseComplexFOLTerm :: Parsec String u (MonadicallySOL (Term Int)) 
parseComplexFOLTerm = try parseConstant 
                    <|> parseFreeVar
                    <|> molecularTermParser parseComplexFOLTerm

opTable :: Monad m => [[Operator String u m (MonadicallySOL (Form Bool))]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

predicationParser :: 
        Parsec String u  (MonadicallySOL (Term Int)) -> Parsec String u (MonadicallySOL (Form Bool))
predicationParser parseTerm = try parseNumbered <|> parseUnnumbered <|> parseVarApp <|> parseLamApp
    where parseUnnumbered = do c <- oneOf "FGHIJKLMNO"
                               let Just n = findIndex (== c) "_FGHIJKLMNO"
                               char '(' *> argParser parseTerm (ppn (-1 * n) AOne)
          parseNumbered = do string "F_"
                             n <- number
                             char '(' *> argParser parseTerm (ppn n AOne)
          parseVarApp   = do c <- oneOf "XYZ"
                             t <- char '(' *>  parseTerm <* char ')'
                             return (SOMApp SOApp :!$: SOMVar [c] :!$: t)
          parseLamApp = do binders <- many1 binder
                           f <- char '[' *> subFormulaParser <* char ']'
                           terms <- char '(' *> sepBy1 parseTerm (char ',') <* char ')'
                           case together 0 f (reverse binders) terms of
                               Just f' -> return f'
                               Nothing -> unexpected "wrong number of lambdas"
              where binder = do oneOf "λ\\"
                                parseFreeVar

                    together n f (v:vs) (t:ts) = together (n+1) (SOMApp SOApp :!$: incLam n f v :!$: t) vs ts
                    together n f [] []  = Just f
                    together n f _ _    = Nothing
