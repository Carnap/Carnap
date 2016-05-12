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
    where subFormulaParser = --formulas wrapped in parentheses
                             parenParser purePropFormulaParser
                             --negations or modalizations of subformulas
                             <|> unaryOpParser [parseNeg] subFormulaParser 
                             --or atom
                             <|> try atomParser
                             <|> schemevarParser

opTable :: Monad m => [[Operator String u m PureForm]]
opTable = [[ Prefix (try parseNeg)], 
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
