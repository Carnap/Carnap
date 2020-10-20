{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses#-}
module Carnap.Languages.PureSecondOrder.Parser
        (msolFormulaParser,psolFormulaParser)
    where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Syntax (foVar)
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses (StandardVarLanguage, BooleanLanguage, IndexedPropLanguage(..), QuantLanguage(..), PolyadicPredicateLanguage(..), TypedLambdaLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.Util.LanguageClasses
import Text.Parsec
import Text.Parsec.Expr
import Data.List (elemIndex)

msolFormulaParser :: Parsec String u (MonadicallySOL (Form Bool))
msolFormulaParser = buildExpressionParser opTable subFormulaParserMSOL 

instance ParsableLex (Form Bool) MonadicallySOLLex where
        langParser = msolFormulaParser

psolFormulaParser :: Parsec String u (PolyadicallySOL (Form Bool))
psolFormulaParser = buildExpressionParser opTablePSOL subFormulaParserPSOL 

instance ParsableLex (Form Bool) PolyadicallySOLLex where
        langParser = psolFormulaParser
    
subFormulaParserMSOL = coreParserMSOL msolFormulaParser subFormulaParserMSOL

subFormulaParserPSOL = coreParserPSOL psolFormulaParser subFormulaParserPSOL

coreParserMSOL recur sfrecur = (parenParser recur <* spaces)
      <|> try (quantifiedSentenceParser parseFreeVar sfrecur)
      <|> try (quantifiedSentenceParser parseMSOLVar sfrecur)
      <|> try (sentenceLetterParser "PQRSTUVW" <* spaces)
      <|> try (msolpredicationParser recur parseSimpleFOTerm)
      <|> unaryOpParser [parseNeg] sfrecur

coreParserPSOL recur sfrecur = (parenParser recur <* spaces)
      <|> try (quantifiedSentenceParser parseFreeVar sfrecur)
      <|> try (quantifiedSentenceParserPSOL sfrecur)
      <|> try (sentenceLetterParser "PQRSTUVW" <* spaces)
      <|> try (psolPredicationParser recur parseSimpleFOTermPSOL)
      <|> unaryOpParser [parseNeg] sfrecur

parseFreeVar :: StandardVarLanguage (FixLang lex (Term Int)) => Parsec String u (FixLang lex (Term Int))
parseFreeVar = choice [try $ do c <- oneOf "vwxyz" 
                                char '_'
                                dig <- many1 digit
                                return $ foVar $ [c] ++ "_" ++ dig
                      ,      do c <- oneOf "vwxyz"
                                return $ foVar [c]
                      ]

parseMSOLVar :: Parsec String u (MonadicallySOL (Form (Int -> Bool)))
parseMSOLVar = choice [try $ do c <- oneOf "XYZ"
                                char '_'
                                dig <- many1 digit
                                return $ SOMVar $ [c] ++ "_" ++ dig
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
        let bf x = subBoundVar (polyVar vstring initArity) x f
        let initForm = if s `elem` "A∀" 
                           then SOPQuant (SOPAll vstring initArity) :!$: (LLam bf) 
                           else SOPQuant (SOPSome vstring initArity) :!$: (LLam bf)
        return $ (iterate incQuant initForm !! arityInt)
    where initArity = AZero :: Arity Int Bool Bool

parseSimpleFOTerm :: Parsec String u (MonadicallySOL (Term Int))
parseSimpleFOTerm = try (parseConstant "abcde") <|> parseFreeVar

parseSimpleFOTermPSOL :: Parsec String u (PolyadicallySOL (Term Int))
parseSimpleFOTermPSOL = try (parseConstant "abcde") <|> parseFreeVar

parseComplexFOLTerm :: Parsec String u (MonadicallySOL (Term Int)) 
parseComplexFOLTerm = try (parseConstant "abcde")
                      <|> parseFreeVar
                      <|> parseFunctionSymbol "fgh" parseComplexFOLTerm

opTable :: Monad m => [[Operator String u m (MonadicallySOL (Form Bool))]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

opTablePSOL :: Monad m => [[Operator String u m (PolyadicallySOL (Form Bool))]]
opTablePSOL = [[ Prefix (try parseNeg)], 
              [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
              [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

msolpredicationParser :: Parsec String u  (MonadicallySOL (Form Bool)) -> Parsec String u  (MonadicallySOL (Term Int)) 
    -> Parsec String u (MonadicallySOL (Form Bool))
msolpredicationParser parseForm parseTerm = try (parsePredicateSymbol "FGHIJKLMNO" parseTerm) <|> parseVarApp <|> parseLamApp parseForm parseTerm
    where parseVarApp   = do c <- oneOf "XYZ"
                             t <- char '(' *>  parseTerm <* char ')'
                             return (SOMApp SOApp :!$: SOMVar [c] :!$: t)

--TODO : typeclass to unify these

parseLamApp parseForm parseTerm = 
        do var <- oneOf "λ\\" *> parseFreeVar
           f <- char '[' *> parseForm <* char ']'
           term <- char '(' *> parseTerm <* char ')'
           let bf x = subBoundVar var x f
           return (SOMApp SOApp :!$: (typedLam (show var) bf) :!$: term)

parseLamAppPSOL parseForm parseTerm = 
        do binders <- many1 binder
           f <- char '[' *> parseForm <* char ']'
           terms <- char '(' *> sepBy1 parsePaddedTerm (char ',') <* char ')'
           case together 0 f (reverse binders) terms of
               Just f' -> return f'
               Nothing -> unexpected "wrong number of lambdas"
    where binder = do oneOf "λ\\"
                      parseFreeVar

          parsePaddedTerm = spaces *> parseTerm <* spaces

          together n f (v:vs) (t:ts) = together (n+1) (SOPApp SOApp :!$: incLam n f v :!$: t) vs ts
          together n f [] []  = Just f
          together n f _ _    = Nothing

psolPredicationParser :: Parsec String u (PolyadicallySOL (Form Bool)) -> Parsec String u (PolyadicallySOL (Term Int)) 
    -> Parsec String u (PolyadicallySOL (Form Bool))
psolPredicationParser parseForm parseTerm = try (parsePredicateSymbol "FGHIJKLMNO" parseTerm) <|> parseVarApp <|> parseLamAppPSOL parseForm parseTerm
    where parseVarApp = do v <- oneOf "XYZ"
                           n <- number
                           char '(' *> spaces
                           terms <- lookAhead (sepBy1 parsePaddedTerm (char ',') <* char ')') -- XXX don't really need to parse terms here.
                           if length terms /= n then unexpected "wrong number of arguments to second order variable"
                                                else return ()
                           parseVarTerms (polyVar (v : show n) AOne)
          parsePaddedTerm = spaces *> parseTerm <* spaces
          parseVarTerms v = do t <- parsePaddedTerm
                               let partialPred = (SOPApp SOApp :!$: v :!$: t)
                               (char ',' *> parseVarTerms (incVar partialPred))
                                    <|> (char ')' *> return partialPred)
