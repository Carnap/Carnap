{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson (logicBookPDCalc,parseLogicBookPD,logicBookPDPlusCalc,parseLogicBookPDPlus) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

data LogicBookPD = SD LogicBookSD | UI | UE 
                 | EI | EE1 | EE2 
                 | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                 deriving Eq

instance Show LogicBookPD where
        show (SD x) = show x
        show UI          = "∀I"
        show UE          = "∀E"
        show EI          = "∃I"
        show EE1         = "∃E"
        show EE2         = "∃E"
        show (Pr _)      = "Assumption"

instance Inference LogicBookPD PureLexiconFOL (Form Bool) where

         ruleOf UI   = universalGeneralization
         ruleOf UE   = universalInstantiation
         ruleOf EI   = existentialGeneralization
         ruleOf EE1  = existentialDerivation !! 0 
         ruleOf EE2  = existentialDerivation !! 1 
         ruleOf (Pr _) = axiom
         ruleOf x@(SD _) = SequentRule (premisesOf x) (conclusionOf x)

         premisesOf (SD x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (SD x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (SD x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI    = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
         restriction EE1   = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2   = Nothing --Since this one does not use the assumption with a fresh object
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _ = Nothing

         isAssumption (SD x) = isAssumption x
         isAssumption _ = False

         isPremise (Pr _) = True
         isPremise _ = False

parseLogicBookPD rtc = try quantRule <|> liftProp 
    where liftProp = do r <- parseLogicBookSD (RuntimeNaturalDeductionConfig mempty mempty)
                        return (map SD r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "PR", "A/EE", "Assumption"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r `elem` ["A/EE"] -> return [SD (AS "/∃E")]
                              | r `elem` [ "PR","Assumption"] -> return [Pr (problemPremises rtc)]

parseLogicBookPDProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPD PureLexiconFOL (Form Bool)]
parseLogicBookPDProof rtc = toDeductionFitchAlt (parseLogicBookPD rtc) bergmannMoorAndNelsonPDFormulaParser --XXX Check parser

logicBookPDCalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parseLogicBookPDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver bergmannMoorAndNelsonPDFormulaParser
    , ndParseForm = bergmannMoorAndNelsonPDFormulaParser
    , ndNotation = ndNotation logicBookSDCalc
    }

data LogicBookPDPlus = PD LogicBookPD | SDPlus LogicBookSDPlus | QN1 | QN2 | QN3 | QN4

instance Show LogicBookPDPlus where
        show (SDPlus x) = show x
        show (PD x) = show x
        show QN1 = "QN"
        show QN2 = "QN"
        show QN3 = "QN"
        show QN4 = "QN"

instance Inference LogicBookPDPlus PureLexiconFOL (Form Bool) where

         ruleOf QN1 = quantifierNegationReplace !! 0
         ruleOf QN2 = quantifierNegationReplace !! 1
         ruleOf QN3 = quantifierNegationReplace !! 2
         ruleOf QN4 = quantifierNegationReplace !! 3
         ruleOf (PD x) = ruleOf x

         premisesOf (SDPlus x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (SDPlus x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (SDPlus x) = indirectInference x
         indirectInference (PD x) = indirectInference x
         indirectInference _ = Nothing 

         restriction (PD x) = restriction x
         restriction _ = Nothing

         isAssumption (SDPlus x) = isAssumption x
         isAssumption (PD x) = isAssumption x
         isAssumption _ = False

         isPremise (PD x) = isPremise x
         isPremise _ = False

parseLogicBookPDPlus rtc = try liftPD <|> try liftProp <|> qn
    where liftPD = do r <- parseLogicBookPD rtc
                      return (map PD r)
          liftProp = do r <- parseLogicBookSDPlus (RuntimeNaturalDeductionConfig mempty mempty)
                        return (map SDPlus r)
          qn = string "QN" >> return [QN1, QN2, QN3, QN4]

parseLogicBookPDPlusProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPDPlus PureLexiconFOL (Form Bool)]
parseLogicBookPDPlusProof rtc = toDeductionFitchAlt (parseLogicBookPDPlus rtc) bergmannMoorAndNelsonPDFormulaParser --XXX Check parser

logicBookPDPlusCalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parseLogicBookPDPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver bergmannMoorAndNelsonPDFormulaParser
    , ndParseForm = bergmannMoorAndNelsonPDFormulaParser
    , ndNotation = ndNotation logicBookSDPlusCalc
    }
