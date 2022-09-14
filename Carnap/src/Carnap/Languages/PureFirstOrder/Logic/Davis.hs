{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Davis (davisQLCalc) where

import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Logic.Davis 
import Carnap.Languages.PurePropositional.Logic.Magnus hiding (Pr)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Logic.Magnus (MagnusQL(..), MagnusQLPlus(..), parseMagnusQLPlus)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Logic.Rules (fitchAssumptionCheck, premConstraint )
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses

data DavisQL = Davis DavisSL | Magnus MagnusQLPlus

instance Show DavisQL where
        show (Davis x) = show x
        show (Magnus x) = show x

instance Inference DavisQL PureLexiconFOL (Form Bool) where
        ruleOf (Magnus x) = ruleOf x

        premisesOf (Davis x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)
        
        conclusionOf (Davis x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference (Davis x) = indirectInference x
        indirectInference (Magnus x) = indirectInference x

        restriction (Magnus (MagnusQL UI))    = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
        restriction (Magnus (MagnusQL EE1))   = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        restriction (Magnus (MagnusQL EE2)) = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2)) 
        restriction (Magnus (MagnusQL (Pr prems))) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n (Davis (DavisSL (MSL CondIntro1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (Davis (DavisSL (MSL CondIntro2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (Davis (DavisSL (MSL BicoIntro1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Davis (DavisSL (MSL BicoIntro2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Davis (DavisSL (MSL BicoIntro3))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Davis (DavisSL (MSL BicoIntro4))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeIntro1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeIntro2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeIntro3))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeIntro4))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeElim1))) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeElim2))) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeElim3))) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n (Davis (DavisSL (MSL NegeElim4))) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction _ _ _ = Nothing

        isAssumption (Magnus x) = isAssumption x
        isAssumption (Davis x) = isAssumption x

        isPremise (Magnus (MagnusQL (Pr prems))) = True
        isPremise _ = False

parseDavisQL rtc = try liftMagnus <|> liftDavis
    where liftMagnus = map Magnus <$> parseMagnusQLPlus rtc
          liftDavis = map Davis <$> parseDavisSL defaultRuntimeDeductionConfig

parseDavisQLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine DavisQL PureLexiconFOL (Form Bool)]
parseDavisQLProof rtc = toDeductionFitch (parseDavisQL rtc) thomasBolducAndZachFOLFormulaParser

davisQLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseDavisQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOLFormulaParser
    , ndParseForm = thomasBolducAndZachFOLFormulaParser
    , ndNotation = ndNotation davisSLCalc
    }
