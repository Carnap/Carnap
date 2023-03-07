{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses#-}
module Carnap.Languages.PureSecondOrder.Parser
        (msolFormulaParser, psolFormulaParser, gamutFormulaParser)
    where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Syntax (foVar)
import Carnap.Languages.PureFirstOrder.Parser (parseFreeVar)
import Carnap.Languages.PurePropositional.Util (isBooleanBinary)
import Carnap.Languages.PurePropositional.Parser (standardOpTable, gamutOpTable)
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses (StandardVarLanguage, BooleanLanguage, IndexedPropLanguage(..), QuantLanguage(..), PolyadicPredicateLanguage(..), TypedLambdaLanguage(..))
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.Util.LanguageClasses
import Text.Parsec
import Text.Parsec.Expr
import Data.List (elemIndex)

msolFormulaParser :: Parsec String u (MonadicallySOL (Form Bool))
msolFormulaParser = buildExpressionParser standardOpTable subFormulaParserMSOL 

instance ParsableLex (Form Bool) MonadicallySOLLex where
        langParser = msolFormulaParser

psolFormulaParser :: Parsec String u (PolyadicallySOL (Form Bool))
psolFormulaParser = buildExpressionParser standardOpTable subFormulaParserPSOL 

gamutFormulaParser :: Parsec String u (PolyadicallySOL (Form Bool))
gamutFormulaParser = buildExpressionParser gamutOpTable subFormulaParserGamut 

instance ParsableLex (Form Bool) PolyadicallySOLLex where
        langParser = psolFormulaParser
    
subFormulaParserMSOL = coreParserMSOL msolFormulaParser subFormulaParserMSOL

subFormulaParserPSOL = coreParserPSOL psolFormulaParser subFormulaParserPSOL

subFormulaParserGamut = coreParserGamut gamutFormulaParser subFormulaParserGamut

coreParserMSOL recur sfrecur = (parenParser recur <* spaces)
      <|> try (quantifiedSentenceParser (parseFreeVar firstOrderVars) sfrecur)
      <|> try (quantifiedSentenceParser parseMSOLVar sfrecur)
      <|> try (sentenceLetterParser sentenceLetters <* spaces)
      <|> try (msolpredicationParser firstOrderVars recur parseFOTerm <* spaces)
      <|> unaryOpParser [parseNeg] sfrecur
      where
        firstOrderVars = ['v'..'z']
        firstOrderConstants = ['a'..'e']
        sentenceLetters = ['P'..'W']
        parseFOTerm = parseSimpleFOTerm firstOrderVars firstOrderConstants

coreParserPSOL recur sfrecur = (parenParser recur <* spaces)
      <|> try (quantifiedSentenceParser (parseFreeVar firstOrderVars) sfrecur)
      <|> try (quantifiedSentenceParserPSOL sfrecur)
      <|> try (sentenceLetterParser sentenceLetters <* spaces)
      <|> try (parsePredicateSymbol predicateSymbols parseFOTerm <* spaces) 
      <|> try (psolPredicationParser firstOrderVars recur parseFOTerm <* spaces)
      <|> unaryOpParser [parseNeg] sfrecur
      where
        firstOrderVars = ['v'..'z']
        firstOrderConstants = ['a'..'e']
        sentenceLetters = ['P'..'W']
        predicateSymbols = ['F'..'O']
        parseFOTerm = parseSimpleFOTermPSOL firstOrderVars firstOrderConstants

coreParserGamut recur sfrecur = (gamutParens <* spaces)
      <|> try (quantifiedSentenceParser (parseFreeVar firstOrderVars) sfrecur)
      <|> try (quantifiedSentenceParserPSOL sfrecur)
      <|> try (sentenceLetterParser sentenceLetters <* spaces)
      <|> try (parsePredicateSymbolNoParen predicateSymbols parseFOTerm <* spaces) 
      <|> try (psolPredicationParserNoParen firstOrderVars recur parseFOTerm <* spaces)
      <|> try (equalsParser parseFOTerm <* spaces)
      <|> try (booleanConstParser <* spaces)
      <|> unaryOpParser [parseNeg] sfrecur
      where
        firstOrderVars = ['s'..'z']
        firstOrderConstants = ['a'..'r']
        sentenceLetters = []
        predicateSymbols = ['A'..'Z']
        parseFOTerm = parseSimpleFOTermPSOL firstOrderVars firstOrderConstants
        gamutParens = (wrappedWith '(' ')' recur <|> wrappedWith '[' ']' recur) >>= boolean
        boolean a = if isBooleanBinary a then return a else unexpected "atomic, negated, or quantified sentence wrapped in parentheses"

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

parseSimpleFOTerm :: [Char] -> [Char] -> Parsec String u (MonadicallySOL (Term Int))
parseSimpleFOTerm firstOrderVars firstOrderConstants = try (parseConstant firstOrderConstants) <|> parseFreeVar firstOrderVars

parseSimpleFOTermPSOL :: [Char] -> [Char] -> Parsec String u (PolyadicallySOL (Term Int))
parseSimpleFOTermPSOL firstOrderVars firstOrderConstants = try (parseConstant firstOrderConstants) <|> parseFreeVar firstOrderVars

opTable :: Monad m => [[Operator String u m (MonadicallySOL (Form Bool))]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

opTablePSOL :: Monad m => [[Operator String u m (PolyadicallySOL (Form Bool))]]
opTablePSOL = [[ Prefix (try parseNeg)], 
              [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
              [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

msolpredicationParser :: [Char] -> Parsec String u  (MonadicallySOL (Form Bool)) -> Parsec String u  (MonadicallySOL (Term Int)) 
    -> Parsec String u (MonadicallySOL (Form Bool))
msolpredicationParser firstOrderVars parseForm parseTerm = 
        try (parsePredicateSymbol "FGHIJKLMNO" parseTerm) 
        <|> parseVarApp 
        <|> parseLamApp firstOrderVars parseForm parseTerm
    where parseVarApp   = do c <- oneOf "XYZ"
                             t <- char '(' *>  parseTerm <* char ')'
                             return (SOMApp SOApp :!$: SOMVar [c] :!$: t)

--TODO : typeclass to unify these

parseLamApp firstOrderVars parseForm parseTerm = 
        do var <- oneOf "λ\\" *> parseFreeVar firstOrderVars
           f <- char '[' *> parseForm <* char ']'
           term <- char '(' *> parseTerm <* char ')'
           let bf x = subBoundVar var x f
           return (SOMApp SOApp :!$: (typedLam (show var) bf) :!$: term)

parseLamAppPSOL firstOrderVars parseForm parseTerm = 
        do binders <- many1 binder
           f <- char '[' *> parseForm <* char ']'
           terms <- char '(' *> sepBy1 parsePaddedTerm (char ',') <* char ')'
           case together 0 f (reverse binders) terms of
               Just f' -> return f'
               Nothing -> unexpected "wrong number of lambdas"
    where binder = do oneOf "λ\\"
                      parseFreeVar firstOrderVars

          parsePaddedTerm = spaces *> parseTerm <* spaces

          together n f (v:vs) (t:ts) = together (n+1) (SOPApp SOApp :!$: incLam n f v :!$: t) vs ts
          together n f [] []  = Just f
          together n f _ _    = Nothing

parseLamAppPSOLNoParen firstOrderVars parseForm parseTerm = 
        do binders <- many1 binder
           f <- char '[' *> parseForm <* char ']'
           terms <- many parseTerm
           case together 0 f (reverse binders) terms of
               Just f' -> return f'
               Nothing -> unexpected "wrong number of lambdas"
    where binder = do oneOf "λ\\"
                      parseFreeVar firstOrderVars

          together n f (v:vs) (t:ts) = together (n+1) (SOPApp SOApp :!$: incLam n f v :!$: t) vs ts
          together n f [] []  = Just f
          together n f _ _    = Nothing

psolPredicationParser :: [Char] -> Parsec String u (PolyadicallySOL (Form Bool)) -> Parsec String u (PolyadicallySOL (Term Int)) 
    -> Parsec String u (PolyadicallySOL (Form Bool))
psolPredicationParser firstOrderVars parseForm parseTerm = 
        parseVarApp <|> parseLamAppPSOL firstOrderVars parseForm parseTerm
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

psolPredicationParserNoParen :: [Char] -> Parsec String u (PolyadicallySOL (Form Bool)) -> Parsec String u (PolyadicallySOL (Term Int)) 
    -> Parsec String u (PolyadicallySOL (Form Bool))
psolPredicationParserNoParen firstOrderVars parseForm parseTerm = 
        parseVarApp <|> parseLamAppPSOLNoParen firstOrderVars parseForm parseTerm
    where parseVarApp = do v <- oneOf "XYZ"
                           n <- number
                           terms <- lookAhead (many parseTerm)
                           if length terms /= n then unexpected "wrong number of arguments to second order variable"
                                                else return ()
                           parseVarTerms (polyVar (v : show n) AOne)
          parseVarTerms v = do t <- parseTerm
                               let partialPred = (SOPApp SOApp :!$: v :!$: t)
                               parseVarTerms (incVar partialPred) <|> return partialPred
