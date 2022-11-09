{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Magnus (magnusQLCalc,magnusQLPlusCalc,MagnusQL(..), MagnusQLPlus(..), parseMagnusQL, parseMagnusQLPlus) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Magnus hiding (Pr)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules (fitchAssumptionCheck)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

--------------------
--  3. System QL  --
--------------------
-- A system of first-order logic resembling system QL from PD Magnus'
-- magnus

data MagnusQL = MagnusSL MagnusSL | UI | UE | EI | EE1 | EE2 | IDI | IDE1 | IDE2 
              | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                    deriving Eq

instance Show MagnusQL where
        show (MagnusSL x) = show x
        show UI          = "∀I"
        show UE          = "∀E"
        show EI          = "∃I"
        show EE1         = "∃E"
        show EE2         = "∃E"
        show IDI         = "=I"
        show IDE1        = "=E"
        show IDE2        = "=E"
        show (Pr _)      = "PR"

instance Inference MagnusQL PureLexiconFOL (Form Bool) where

         ruleOf UI   = universalGeneralization
         ruleOf UE   = universalInstantiation
         ruleOf EI   = existentialGeneralization
         ruleOf EE1  = existentialDerivation !! 0 
         ruleOf EE2  = existentialDerivation !! 1 
         ruleOf IDI  = eqReflexivity

         ruleOf IDE1   = leibnizLawVariations !! 0
         ruleOf IDE2   = leibnizLawVariations !! 1
         ruleOf x@(MagnusSL _) = premisesOf x ∴ conclusionOf x
         ruleOf (Pr _) = axiom

         premisesOf (MagnusSL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (MagnusSL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (MagnusSL x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI    = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
         restriction EE1   = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2   = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2)) 
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _ = Nothing

         globalRestriction (Left ded) n (MagnusSL CondIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (MagnusSL CondIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (MagnusSL BicoIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusSL BicoIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusSL BicoIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusSL BicoIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusSL NegeIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusSL NegeIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusSL NegeIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusSL NegeIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusSL NegeElim1) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (MagnusSL NegeElim2) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (MagnusSL NegeElim3) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (MagnusSL NegeElim4) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction _ _ _ = Nothing

         isAssumption (MagnusSL x) = isAssumption x
         isAssumption _ = False

         isPremise (Pr _) = True
         isPremise _ = False

parseMagnusQL rtc = try quantRule <|> liftProp 
    where liftProp =  map MagnusSL <$> parseMagnusSL (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E","PR"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r == "PR" -> return [Pr (problemPremises rtc)]
                              | r == "=I" -> return [IDI]
                              | r == "=E" -> return [IDE1,IDE2]

parseMagnusQLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine MagnusQL PureLexiconFOL (Form Bool)]
parseMagnusQLProof rtc = toDeductionFitch (parseMagnusQL rtc) magnusFOLFormulaParser

magnusQLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseMagnusQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver magnusFOLFormulaParser
    , ndParseForm = magnusFOLFormulaParser
    , ndNotation = ndNotation magnusSLCalc
    }

--------------------
--  3. System QL Plus  --
--------------------
-- A system of first-order logic resembling system QL from PD Magnus'
-- forallx, with derived rules added

data MagnusQLPlus = MagnusQL MagnusQL | Plus MagnusSLPlus | QN1 | QN2 | QN3 | QN4
      deriving Eq

instance Show MagnusQLPlus where
        show (MagnusQL x) = show x
        show (Plus x) = show x
        show QN1 = "QN"
        show QN2 = "QN"
        show QN3 = "QN"
        show QN4 = "QN"

instance Inference MagnusQLPlus PureLexiconFOL (Form Bool) where

         ruleOf QN1 = quantifierNegationReplace !! 0
         ruleOf QN2 = quantifierNegationReplace !! 1
         ruleOf QN3 = quantifierNegationReplace !! 2
         ruleOf QN4 = quantifierNegationReplace !! 3
         ruleOf (Plus AndComm) = andCommutativity !! 0
         ruleOf (Plus CommAnd) = andCommutativity !! 1
         ruleOf (Plus OrComm)  = orCommutativity !! 0
         ruleOf (Plus CommOr)  = orCommutativity !! 1
         ruleOf (Plus IffComm) = iffCommutativity !! 0 
         ruleOf (Plus CommIff) = iffCommutativity !! 1
         ruleOf (Plus DNRep)   = doubleNegation !! 0
         ruleOf (Plus RepDN)   = doubleNegation !! 1
         ruleOf (Plus MCRep)   = materialConditional !! 0
         ruleOf (Plus RepMC)   = materialConditional !! 1
         ruleOf (Plus MCRep2)  = materialConditional !! 2
         ruleOf (Plus RepMC2)  = materialConditional !! 3
         ruleOf (Plus BiExRep) = biconditionalExchange !! 0
         ruleOf (Plus RepBiEx) = biconditionalExchange !! 1
         ruleOf (Plus DM1)     = deMorgansLaws !! 0
         ruleOf (Plus DM2)     = deMorgansLaws !! 1
         ruleOf (Plus DM3)     = deMorgansLaws !! 2
         ruleOf (Plus DM4)     = deMorgansLaws !! 3
         ruleOf (Plus x)       = map liftSequent (premisesOf x) ∴ liftSequent (conclusionOf x)
         ruleOf (MagnusQL x)   = ruleOf x

         premisesOf (MagnusQL (MagnusSL x)) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (MagnusQL (MagnusSL x)) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (MagnusQL x) = indirectInference x
         indirectInference _ = Nothing

         restriction (MagnusQL x) = restriction x
         restriction _ = Nothing

         globalRestriction (Left ded) n (MagnusQL (MagnusSL CondIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (MagnusQL (MagnusSL CondIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (MagnusQL (MagnusSL BicoIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusQL (MagnusSL BicoIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusQL (MagnusSL BicoIntro3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusQL (MagnusSL BicoIntro4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeIntro3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeIntro4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeElim1)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeElim2)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeElim3)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (MagnusQL (MagnusSL NegeElim4)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction _ _ _ = Nothing


         isAssumption (MagnusQL x) = isAssumption x
         isAssumption _ = False

         isPremise (MagnusQL x) = True
         isPremise _ = False

parseMagnusQLPlus rtc = try liftQL <|> try liftPlus <|> foPlus
    where liftQL = map MagnusQL <$> parseMagnusQL rtc
          liftPlus = map Plus <$> parseMagnusSLPlus (defaultRuntimeDeductionConfig)
          foPlus = string "QN" >> return [QN1,QN2,QN3,QN4]

parseMagnusQLPlusProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine MagnusQLPlus PureLexiconFOL (Form Bool)]
parseMagnusQLPlusProof rtc = toDeductionFitch (parseMagnusQLPlus rtc) magnusFOLFormulaParser

magnusQLPlusCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseMagnusQLPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver magnusFOLFormulaParser
    , ndParseForm = magnusFOLFormulaParser
    , ndNotation = ndNotation magnusSLCalc
    }
