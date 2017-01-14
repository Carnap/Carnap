module Carnap.Languages.ModalPropositional.Parser
    (modalPropFormulaParser)
where

import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, ModalLanguage, IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Carnap.Core.Unification.Unification

modalPropFormulaParser :: Monad m => ParsecT String u m ModalForm
modalPropFormulaParser = buildExpressionParser opTable subFormulaParser
    --subformulas are either
    where subFormulaParser = --formulas wrapped in parentheses
                             parenParser modalPropFormulaParser
                             --negations of subformulas
                             <|> unaryOpParser [parseNeg, parsePos, parseNec]
                                subFormulaParser
                             --or atom
                             <|> try (atomicSentenceParser "PQRSTUVW")
                             <|> schemevarParser

opTable :: Monad m => [[Operator String u m ModalForm]]
opTable = [[ Prefix (try parseNeg), Prefix (try parseNec), Prefix (try parsePos)],
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
