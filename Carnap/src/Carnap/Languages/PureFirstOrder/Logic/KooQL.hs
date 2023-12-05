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

--------------------------------------------------------
--2. Classical First-Order Logic
--------------------------------------------------------

data KooQL =  SL KooSL
                | UD  | UI  | EG  | EI | QN1 | QN2  | QN3  | QN4 | QN5 | QN6 | QN7 | QN8
                | LL1 | LL2 | EL1 | EL2 | ID  | SM  | ALL1 | ALL2 | AV1 | AV2
                | DER (ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))
                | PR (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
               deriving (Eq)

instance Show KooQL where
        show (PR _)  = "PR"
        show UD      = "UD"
        show UI      = "UI"
        show EG      = "EG"
        show EI      = "EI"
        show (DER _) = "Derived"
        show QN1     = "QN"
        show QN2     = "QN"
        show QN3     = "QN"
        show QN4     = "QN"
        show QN5     = "QN"
        show QN6     = "QN"
        show QN7     = "QN"
        show QN8     = "QN"
        show ID      = "Id"
        show LL1     = "LL"
        show LL2     = "LL"
        show ALL1    = "LL"
        show ALL2    = "LL"
        show EL1     = "EL"
        show EL2     = "EL"
        show SM      = "Sm"
        show (SL x)  = show x
        show AV1     = "AV"
        show AV2     = "AV"

instance Inference KooQL PureLexiconFOL (Form Bool) where
     ruleOf (PR _)    = axiom
     ruleOf UI        = universalInstantiation
     ruleOf EG        = existentialGeneralization
     ruleOf UD        = universalGeneralization
     ruleOf EI        = existentialInstantiation
     ruleOf QN1       = quantifierNegation !! 0
     ruleOf QN2       = quantifierNegation !! 1
     ruleOf QN3       = quantifierNegation !! 2
     ruleOf QN4       = quantifierNegation !! 3
     ruleOf QN5       = quantifierDoubleNegationReplace !! 0
     ruleOf QN6       = quantifierDoubleNegationReplace !! 1
     ruleOf QN7       = quantifierDoubleNegationReplace !! 2
     ruleOf QN8       = quantifierDoubleNegationReplace !! 3
     ruleOf LL1       = leibnizLawVariations !! 0
     ruleOf LL2       = leibnizLawVariations !! 1
     ruleOf ALL1      = antiLeibnizLawVariations !! 0
     ruleOf ALL2      = antiLeibnizLawVariations !! 1
     ruleOf EL1       = euclidsLawVariations !! 0
     ruleOf EL2       = euclidsLawVariations !! 1
     ruleOf ID        = eqReflexivity
     ruleOf SM        = eqSymmetry
     ruleOf AV1       = quantifierExchange !! 0
     ruleOf AV2       = quantifierExchange !! 2

     premisesOf (SL x) = map liftSequent (premisesOf x)
     premisesOf (DER r) = multiCutLeft r
     premisesOf x     = upperSequents (ruleOf x)

     conclusionOf (SL x) = liftSequent (conclusionOf x)
     conclusionOf (DER r) = multiCutRight r
     conclusionOf x   = lowerSequent (ruleOf x)

     restriction (PR prems) = Just (premConstraint prems)
     restriction _          = Nothing
     
     globalRestriction (Left ded) n UD = Just (montagueNewUniversalConstraint [tau] ded n)
     globalRestriction (Left ded) n EI = Just (montagueNewExistentialConstraint [tau] ded n)
     globalRestriction _ _ _ = Nothing

     indirectInference (SL x) = indirectInference x
     indirectInference UD  = Just PolyProof
     indirectInference _ = Nothing

parseKooQL :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [KooQL]
parseKooQL rtc = try quantRule <|> liftProp
    where liftProp = do r <- parseKooSL (defaultRuntimeDeductionConfig)
                        return (map SL r)
          quantRule = do r <- choice (map (try . string) ["PR", "UI", "UD", "EG", "EI", "QN","LL","EL","Id","Sm","AV", "D-"])
                         case r of 
                            r | r == "PR" -> return [PR $ problemPremises rtc]
                              | r == "UI" -> return [UI]
                              | r == "UD" -> return [UD]
                              | r == "EG" -> return [EG]
                              | r == "EI" -> return [EI]
                              | r == "QN" -> return [QN1,QN2,QN3,QN4,QN5,QN6,QN7,QN8]
                              | r == "LL" -> return [LL1,LL2,ALL1,ALL2]
                              | r == "Sm" -> return [SM]
                              | r == "EL" -> return [EL1,EL2]
                              | r == "Id" -> return [ID]
                              | r == "AV" -> return [AV1,AV2]
                              | r == "D-" ->  do rn <- many1 upper
                                                 case M.lookup rn (derivedRules rtc) of
                                                    Just r  -> return [DER r]
                                                    Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

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

parseKooQLProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine KooQL PureLexiconFOL (Form Bool)]
parseKooQLProof ders = toDeductionMontague (parseKooQL ders) kooQLFormulaParser

kooQLCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseKooQLProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    , ndNotation = kooSLNotation
    , ndParseForm = kooQLFormulaParser
    , ndParseSeq = parseSeqOver kooQLFormulaParser
    }
