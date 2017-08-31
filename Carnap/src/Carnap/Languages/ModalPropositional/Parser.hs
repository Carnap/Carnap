module Carnap.Languages.ModalPropositional.Parser
    (modalPropFormulaParser,worldTheoryPropFormulaParser)
where

import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage, ModalLanguage, IndexedPropLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Carnap.Core.Unification.Unification

--subformulas are either
coreSubformulaParser fp = 
        --formulas wrapped in parentheses
        parenParser fp
        --negations of subformulas
        <|> unaryOpParser [parseNeg, parsePos, parseNec]
           (coreSubformulaParser fp)
        --or atoms
        <|> try (sentenceLetterParser "PQRSTUVW")
        <|> schemevarParser

modalPropFormulaParser :: Monad m => ParsecT String u m ModalForm
modalPropFormulaParser = buildExpressionParser opTable subFormulaParser 
    where subFormulaParser = coreSubformulaParser modalPropFormulaParser

worldTheoryPropFormulaParser :: Monad m => ParsecT String u m WorldTheoryForm
worldTheoryPropFormulaParser = buildExpressionParser worldTheoryOpTable subFormulaParser 
    where subFormulaParser = coreSubformulaParser worldTheoryPropFormulaParser

opTable :: Monad m => [[Operator String u m ModalForm]]
opTable = [[Prefix (try parseNeg), Prefix (try parseNec), Prefix (try parsePos)],
          [ Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [ Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

worldTheoryOpTable :: Monad m => [[Operator String u m WorldTheoryForm]]
worldTheoryOpTable = [[Postfix (try parseWorldIndex)],
                     [ Prefix (try parseNeg), Prefix (try parseNec), Prefix (try parsePos)],
                     [ Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
                     [ Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

parseWorldIndex :: Monad m => ParsecT String u m (WorldTheoryForm -> WorldTheoryForm)
parseWorldIndex = do char '/'
                     digits <- many1 digit
                     return $ \x -> x `atWorld` (read digits)
