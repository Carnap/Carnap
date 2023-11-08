{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.KooQL
        (parseKooQLProof, kooQLCalc)
    where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Text.Parsec.Expr
import Control.Monad.Identity
import Carnap.Core.Unification.Unification (applySub)
import Carnap.Core.Data.Types
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineMontague, hoProcessLineMontagueMemo)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Logic.Rules (axiom,premConstraint)
import Carnap.Languages.PurePropositional.Logic.KooSL
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PureFirstOrder.Logic.KalishAndMontague

--------------------------------------------------------
--2. Classical First-Order Logic
--------------------------------------------------------

kooQLParserOptions :: FirstOrderParserOptions PureLexiconFOL u Identity
kooQLParserOptions = FirstOrderParserOptions 
                         { atomicSentenceParser = \x -> kooParsePredicateSymbol "ABCDEFGHIJKLMNO" x
                                                        <|> sentenceLetterParser "PQRSTUVWXYZ"
                                                        <|> equalsParser x 
                                                        <|> inequalityParserStrict x
                         , quantifiedSentenceParser' = kooQuantifiedSentenceParser
                         , freeVarParser = parseFreeVar "ijklmnopqrstuvwxyz"
                         , constantParser = Just (parseConstant "abcdefgh") 
                         , functionParser = Just (\x -> kooParseFunctionSymbol "abcdefgh" x)
                         , hasBooleanConstants = False
                         , parenRecur = \opt recurWith  -> parenParser (recurWith opt) >>= boolean
                         , opTable = kooOpTable
                         , finalValidation = const (pure ())
                         }
                    where boolean a = if isBoolean a then return a else unexpected "atomic or quantified sentence wrapped in parentheses"
                         
kooSubFormulaParser :: ( BoundVars lex
                        , BooleanLanguage (FixLang lex (Form Bool))
                        , BooleanConstLanguage (FixLang lex (Form Bool))
                        , QuantLanguage (FixLang lex (Form Bool)) (FixLang lex (Term Int))
                        ) =>
    (FirstOrderParserOptions lex u Identity -> Parsec String u (FixLang lex (Form Bool))) -> FirstOrderParserOptions lex u Identity
        -> Parsec String u (FixLang lex (Form Bool))
kooSubFormulaParser fp opts =   try (parenRecur opts opts fp <* spaces)
                                <|> try (unaryOpParser [parseNegStrict] (kooSubFormulaParser fp opts))
                                <|> try (quantifiedSentenceParser' opts vparser (kooSubFormulaParser fp opts) <* spaces)
                                <|> (atomicSentenceParser opts tparser <* spaces)
                                <|> if hasBooleanConstants opts then try (booleanConstParser <* spaces) else parserZero
    where cparser = case constantParser opts of Just c -> c
                                                Nothing -> mzero
          --Function symbols, if there are any
          fparser = case functionParser opts of Just f -> f
                                                Nothing -> const mzero
          --Free variables
          vparser = freeVarParser opts 
          --Terms
          tparser = try (fparser tparser) <|> try cparser <|> vparser 

kooParserFromOptions opts = do  f <- buildExpressionParser (opTable opts) subformulaParser 
                                finalValidation opts f
                                return f
                            where subformulaParser = kooSubFormulaParser kooParserFromOptions (opts {finalValidation = const (return ())})

kooQLFormulaParser :: Parsec String u PureFOLForm
kooQLFormulaParser = kooParserFromOptions kooQLParserOptions

parseKooQLProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine MontagueQCCalc PureLexiconFOL (Form Bool)]
parseKooQLProof ders = toDeductionMontague (parseMontagueQCCalc ders) kooQLFormulaParser

kooQLCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseKooQLProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    , ndNotation = kooSLNotation
    , ndParseForm = kooQLFormulaParser
    , ndParseSeq = parseSeqOver kooQLFormulaParser
    }
