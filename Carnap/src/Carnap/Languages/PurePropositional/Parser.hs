module Carnap.Languages.PurePropositional.Parser
    (purePropFormulaParser)
    where

import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr

--this parses as much formula as it can, but is happy to return an output if the
--initial segment of a string is a formula
prePurePropFormulaParser :: Monad m => ParsecT String u m PureForm
prePurePropFormulaParser = buildExpressionParser opTable subFormulaParser
    --subformulas are either
    where subFormulaParser = (parenParser prePurePropFormulaParser <* spaces)  --formulas wrapped in parentheses
                          <|> unaryOpParser [parseNeg] subFormulaParser --negations or modalizations of subformulas
                          <|> try (atomicSentenceParser <* spaces)--or atoms
                          <|> (schemevarParser <* spaces)

--this requires that the whole string be a formula, although it allows
--trailing spaces.
purePropFormulaParser :: Monad m => ParsecT String u m PureForm
purePropFormulaParser = do e <- prePurePropFormulaParser
                           eof
                           return e

opTable :: Monad m => [[Operator String u m PureForm]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
