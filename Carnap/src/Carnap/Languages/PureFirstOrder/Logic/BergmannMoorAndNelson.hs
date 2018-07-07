{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson (logicBookPDCalc,parseLogicBookPD) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

data LogicBookPD = LogicBookSD P.LogicBookSD | UI | UE 
                 | EI | EE1 | EE2 
                 | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                 deriving Eq

instance Show LogicBookPD where
        show (LogicBookSD x) = show x
        show UI          = "∀I"
        show UE          = "∀E"
        show EI          = "∃I"
        show EE1         = "∃E"
        show EE2         = "∃E"
        show (Pr _)      = "PR"

instance Inference LogicBookPD PureLexiconFOL (Form Bool) where

         ruleOf UI   = universalGeneralization
         ruleOf UE   = universalInstantiation
         ruleOf EI   = existentialGeneralization
         ruleOf EE1  = existentialDerivation !! 0 
         ruleOf EE2  = existentialDerivation !! 1 
         ruleOf (Pr _) = axiom

         premisesOf (LogicBookSD x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (LogicBookSD x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (LogicBookSD x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI    = Just (eigenConstraint (SeqT 1) (SS (lall "v" $ phi' 1)) (fogamma 1))
         restriction EE1   = Just (eigenConstraint (SeqT 1) (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2   = Nothing --Since this one does not use the assumption with a fresh object
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _ = Nothing

         isAssumption (LogicBookSD x) = isAssumption x
         isAssumption _ = False

parseLogicBookPD rtc = try quantRule <|> liftProp 
    where liftProp = do r <- P.parseFitchPropLogic (RuntimeNaturalDeductionConfig mempty mempty)
                        return (map LogicBookSD r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "PR"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r == "PR" -> return [Pr (problemPremises rtc)]

parseLogicBookPDProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPD PureLexiconFOL (Form Bool)]
parseLogicBookPDProof rtc = toDeductionFitch (parseLogicBookPD rtc) bergmannMoorAndNelsonPDFormulaParser --XXX Check parser

logicBookPDCalc = NaturalDeductionCalc
    { ndRenderer = FitchStyle
    , ndParseProof = parseLogicBookPDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = folSeqParser
    }
