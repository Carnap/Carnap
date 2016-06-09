module Carnap.Languages.ModalPropositional.Parser
    (modalPropFormulaParser, foDemo)
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
                             <|> try atomicSentenceParser
                             <|> schemevarParser

opTable :: Monad m => [[Operator String u m ModalForm]]
opTable = [[ Prefix (try parseNeg), Prefix (try parseNec), Prefix (try parsePos)],
          [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
          [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]

foDemo = do
  lhs <- getLine
  if lhs /= ""
    then do
      rhs <- getLine
      let t1 = parse modalPropFormulaParser "left hand side" lhs
      let t2 = parse modalPropFormulaParser "right hand side" rhs
      case (t1, t2) of
        (Left err, _) -> print err
        (_, Left err) -> print err
        (Right x, Right y) -> print $ founify [x :=: y] []
      foDemo
    else return ()
