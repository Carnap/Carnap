module Carnap.Core.ModelChecking.Parser() where

import Carnap.Core.ModelChecking.ModelFinder
import Carnap.Languages.Util.LanguageClasses (BooleanLanguage)
import Carnap.Languages.Util.GenericParsers
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Char

smtParser :: Monad m => ParsecT String u m (MLang nm)
smtParser = buildExpressionParser opTable subFormulaParser
    --subformulas are either
    where subFormulaParser =  parenParser smtParser
                          <|> unaryOpParser [parseNeg] subFormulaParser


opTable :: Monad m => [[Operator String u m (MLang nm)]]
opTable = [[ Prefix (try parseNeg)],
           [Infix (try parseOr) AssocLeft, Infix (try parseAnd) AssocLeft],
           [Infix (try parseIf) AssocNone, Infix (try parseIff) AssocNone]]
