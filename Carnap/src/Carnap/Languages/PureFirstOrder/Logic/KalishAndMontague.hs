{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.KalishAndMontague
        (MontagueQCCalc(..), parseMontagueQCCalc, montagueQCCalc)
    where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Unification.Unification (applySub)
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineMontague, hoProcessLineMontagueMemo)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules (axiom,premConstraint)
import Carnap.Languages.PureFirstOrder.Logic.Rules

--------------------------------------------------------
--2. Classical First-Order Logic
--------------------------------------------------------

data MontagueQCCalc =  SL P.MontagueSC
                | UD  | UI  | EG  | EI | QN1 | QN2  | QN3  | QN4  
                | LL1 | LL2 | EL1 | EL2 | ID  | SM  | ALL1 | ALL2
                | DER (ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))
                | PR (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
               deriving (Eq)

instance Show MontagueQCCalc where
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
        show ID      = "Id"
        show LL1     = "LL"
        show LL2     = "LL"
        show ALL1    = "LL"
        show ALL2    = "LL"
        show EL1     = "EL"
        show EL2     = "EL"
        show SM      = "Sm"
        show (SL x)  = show x

instance Inference MontagueQCCalc PureLexiconFOL (Form Bool) where
     ruleOf (PR _)    = axiom
     ruleOf UI        = universalInstantiation
     ruleOf EG        = existentialGeneralization
     ruleOf UD        = universalGeneralization
     ruleOf EI        = existentialInstantiation
     ruleOf QN1       = quantifierNegation !! 0
     ruleOf QN2       = quantifierNegation !! 1
     ruleOf QN3       = quantifierNegation !! 2
     ruleOf QN4       = quantifierNegation !! 3
     ruleOf LL1       = leibnizLawVariations !! 0
     ruleOf LL2       = leibnizLawVariations !! 1
     ruleOf ALL1      = antiLeibnizLawVariations !! 0
     ruleOf ALL2      = antiLeibnizLawVariations !! 1
     ruleOf EL1       = euclidsLawVariations !! 0
     ruleOf EL2       = euclidsLawVariations !! 1
     ruleOf ID        = eqReflexivity
     ruleOf SM        = eqSymmetry

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

parseMontagueQCCalc :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [MontagueQCCalc]
parseMontagueQCCalc rtc = try quantRule <|> liftProp
    where liftProp = do r <- P.parseMontagueSC (defaultRuntimeDeductionConfig)
                        return (map SL r)
          quantRule = do r <- choice (map (try . string) ["PR", "UI", "UD", "EG", "EI", "QN","LL","EL","Id","Sm","D-"])
                         case r of 
                            r | r == "PR" -> return [PR $ problemPremises rtc]
                              | r == "UI" -> return [UI]
                              | r == "UD" -> return [UD]
                              | r == "EG" -> return [EG]
                              | r == "EI" -> return [EI]
                              | r == "QN" -> return [QN1,QN2,QN3,QN4]
                              | r == "LL" -> return [LL1,LL2,ALL1,ALL2]
                              | r == "Sm" -> return [SM]
                              | r == "EL" -> return [EL1,EL2]
                              | r == "Id" -> return [ID]
                              | r == "D-" ->  do rn <- many1 upper
                                                 case M.lookup rn (derivedRules rtc) of
                                                    Just r  -> return [DER r]
                                                    Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

parseMontagueQCProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine MontagueQCCalc PureLexiconFOL (Form Bool)]
parseMontagueQCProof ders = toDeductionMontague (parseMontagueQCCalc ders) folFormulaParser

montagueQCCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseMontagueQCProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    }
