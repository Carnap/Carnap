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
import Data.List (elemIndex)

msolFormulaParser :: Parsec String u (MonadicallySOL (Form Bool))
msolFormulaParser = buildExpressionParser opTable subFormulaParser 
    
subFormulaParser = coreParser msolFormulaParser subFormulaParser

coreParser recur sfrecur = (parenParser recur <* spaces)
      <|> try (quantifiedSentenceParser parseFreeVar sfrecur)
      <|> try (quantifiedSentenceParser parseMSOLVar sfrecur)
      <|> try (sentenceLetterParser "PQRSTUVW" <* spaces)
      <|> try (predicationParser recur parseSimpleFOTerm)
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

quantifiedSentenceParserPSOL :: Parsec String u (PolyadicallySOL (Form Bool)) -> Parsec String u (PolyadicallySOL (Form Bool))
quantifiedSentenceParserPSOL formulaParser = do
        s  <- oneOf "AE∀∃"
        v  <- oneOf "XYZ"
        arityInt <- number
        let vstring = v : show arityInt
        spaces
        f <- formulaParser
        let bf x = subBoundVar (SOPVar vstring AOne) x f
        let initForm = if s `elem` "A∀" 
                           then SOPQuant (SOPAll vstring AOne) :!$: (LLam bf) 
                           else SOPQuant (SOPSome vstring AOne) :!$: (LLam bf)
        return $ (iterate incQuant initForm !! arityInt)

parseSimpleFOTerm :: Parsec String u (MonadicallySOL (Term Int))
parseSimpleFOTerm = try (parseConstant "abcde") <|> parseFreeVar

parseComplexFOLTerm :: Parsec String u (MonadicallySOL (Term Int)) 
parseComplexFOLTerm = try (parseConstant "abcde")
                      <|> parseFreeVar
                      <|> parseFunctionSymbol "fgh" parseComplexFOLTerm

opTable :: Monad m => [[Operator String u m (MonadicallySOL (Form Bool))]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

predicationParser :: Parsec String u  (MonadicallySOL (Form Bool)) -> Parsec String u  (MonadicallySOL (Term Int)) -> Parsec String u (MonadicallySOL (Form Bool))
predicationParser parseForm parseTerm = try parseNumbered <|> parseUnnumbered <|> parseVarApp <|> parseLamApp
    where parseUnnumbered = do c <- oneOf "FGHIJKLMNO"
                               let Just n = elemIndex c "_FGHIJKLMNO"
                               char '(' *> argParser parseTerm (ppn (-1 * n) AOne)
          parseNumbered = do string "F_"
                             n <- number
                             char '(' *> argParser parseTerm (ppn n AOne)
          parseVarApp   = do c <- oneOf "XYZ"
                             t <- char '(' *>  parseTerm <* char ')'
                             return (SOMApp SOApp :!$: SOMVar [c] :!$: t)
          parseLamApp = do binders <- many1 binder
                           f <- char '[' *> parseForm <* char ']'
                           terms <- char '(' *> sepBy1 parseTerm (char ',') <* char ')'
                           case together 0 f (reverse binders) terms of
                               Just f' -> return f'
                               Nothing -> unexpected "wrong number of lambdas"
              where binder = do oneOf "λ\\"
                                parseFreeVar

                    together n f (v:vs) (t:ts) = together (n+1) (SOMApp SOApp :!$: incLam n f v :!$: t) vs ts
                    together n f [] []  = Just f
                    together n f _ _    = Nothing

psolPredicationParser :: Parsec String u (PolyadicallySOL (Form Bool)) -> Parsec String u (PolyadicallySOL (Term Int)) 
    -> Parsec String u (PolyadicallySOL (Form Bool))
psolPredicationParser parseForm parseTerm = parseVarApp
    where parseVarApp = do v <- oneOf "XYZ"
                           n <- number
                           char '('
                           terms <- lookAhead (sepBy1 parseTerm (char ',') <* char ')') -- XXX don't really need to parse terms here.
                           if length terms /= n then unexpected "wrong number of arguments to second order variable"
                                                else return ()
                           parseVarTerms (SOPVar (v : show n) AOne)
          parseVarTerms v = do t <- parseTerm
                               let partialPred = (SOPApp SOApp :!$: v :!$: t)
                               (char ',' *> parseVarTerms (incVar partialPred))
                                    <|> (char ')' *> return partialPred)


