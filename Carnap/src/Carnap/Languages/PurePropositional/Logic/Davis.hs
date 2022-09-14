{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Davis 
(davisSLCalc, parseDavisSL, DavisSL(..)) where

import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Logic.Magnus (MagnusSL(..), MagnusSLPlus(..), parseMagnusSLPlus)
import Carnap.Languages.PurePropositional.Logic.Rules 
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach (thomasBolducAndZachNotation)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses

data DavisSL = DavisSL MagnusSLPlus | TautAndL | TautAndR | TautOrL | TautOrR

instance Show DavisSL where
        show (DavisSL (MSL ConjIntro))  = "∧I"
        show (DavisSL (MSL ConjElim1))  = "∧E"
        show (DavisSL (MSL ConjElim2))  = "∧E"
        show (DavisSL x) = show x
        show TautAndL = "Taut"
        show TautAndR = "Taut"
        show TautOrL = "Taut"
        show TautOrR = "Taut"

instance Inference DavisSL PurePropLexicon (Form Bool) where
        ruleOf (DavisSL Dilemma) = constructiveDilemma
        ruleOf (DavisSL x) = ruleOf x
        ruleOf TautAndL = andIdempotence !! 0
        ruleOf TautAndR = andIdempotence !! 1
        ruleOf TautOrL = orIdempotence !! 0
        ruleOf TautOrR = orIdempotence !! 1

        indirectInference (DavisSL x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (DavisSL x) = isAssumption x
        isAssumption _ = False

        isPremise (DavisSL x) = isPremise x
        isPremise _ = False

        restriction (DavisSL x) = restriction x
        restriction _ = Nothing

        globalRestriction (Left ded) n (DavisSL (MSL CondIntro1))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (DavisSL (MSL CondIntro2))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (DavisSL (MSL BicoIntro1))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (DavisSL (MSL BicoIntro2))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (DavisSL (MSL BicoIntro3))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (DavisSL (MSL BicoIntro4))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (DavisSL (MSL NegeIntro1))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (DavisSL (MSL NegeIntro2))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (DavisSL (MSL NegeIntro3))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (DavisSL (MSL NegeIntro4))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (DavisSL (MSL NegeElim1)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n (DavisSL (MSL NegeElim2)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n (DavisSL (MSL NegeElim3)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n (DavisSL (MSL NegeElim4)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction _ _ _ = Nothing

parseDavisSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [DavisSL]
parseDavisSL rtc = (map DavisSL <$> parseMagnusSLPlus rtc) <|> (string "Taut" >> return [TautOrL, TautOrR, TautAndL, TautAndR])

parseDavisSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine DavisSL PurePropLexicon (Form Bool)]
parseDavisSLProof rtc = toDeductionFitch (parseDavisSL rtc) (purePropFormulaParser thomasBolducZachOpts)

davisSLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseDavisSLProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZachOpts)
    , ndParseForm = purePropFormulaParser thomasBolducZachOpts
    , ndNotation = thomasBolducAndZachNotation
    }
