module Carnap.Languages.PurePropositional.Parser (purePropFormulaParser) where

import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

--this parses as much formula as it can, but is happy to return an output if the
--initial segment of a string is a formula
purePropFormulaParser :: Monad m => String -> ParsecT String u m PureForm
purePropFormulaParser s = buildExpressionParser opTable subFormulaParser
    --subformulas are either
    where subFormulaParser = (parenParser (purePropFormulaParser s) <* spaces)  --formulas wrapped in parentheses
                          <|> unaryOpParser [parseNeg] subFormulaParser --negations or modalizations of subformulas
                          <|> try (atomicSentenceParser s <* spaces)--or atoms
                          <|> (schemevarParser <* spaces)

opTable :: Monad m => [[Operator String u m PureForm]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
