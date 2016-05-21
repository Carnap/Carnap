module Carnap.Languages.PurePropositional.Parser
    (purePropFormulaParser)
    where

import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
                      
purePropFormulaParser :: Monad m => ParsecT String u m PureForm
purePropFormulaParser = buildExpressionParser opTable subFormulaParser 
    --subformulas are either
    where subFormulaParser = parenParser purePropFormulaParser  --formulas wrapped in parentheses
                          <|> unaryOpParser [parseNeg] subFormulaParser --negations or modalizations of subformulas
                          <|> try atomParser --or atoms
                          <|> schemevarParser

opTable :: Monad m => [[Operator String u m PureForm]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
