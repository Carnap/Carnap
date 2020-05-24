{-#LANGUAGE  FlexibleContexts, RankNTypes, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.DefiniteDescription.Logic.Gamut (gamutNDDescCalc, parseGamutNDDesc, ofDefiniteDescSys) where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.DefiniteDescription.Syntax
import Carnap.Languages.DefiniteDescription.Parser
import Carnap.Languages.PurePropositional.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Syntax (fogamma, OpenLexiconFOL)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (fitchAssumptionCheck)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Text.Parsec

data GamutNDDesc = GNDP GamutNDPlus
    deriving Eq

instance Show GamutNDDesc where
        show (GNDP x) = show x

instance Inference GamutNDDesc FregeanDescLex (Form Bool) where
        ruleOf r = premisesOf r ∴ conclusionOf r

        premisesOf (GNDP x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf (GNDP x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference (GNDP x) = indirectInference x
        indirectInference _ = Nothing

        restriction (GNDP (CoreP InA))   = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
        restriction (GNDP (CoreP ElimE)) = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        restriction _          = Nothing

        globalRestriction (Left ded) n (GNDP (CoreP InA))   = Just (notAssumedConstraint n ded (taun 1 :: FregeanDescSeq (Term Int)))
        globalRestriction (Left ded) n (GNDP (CoreP ElimE)) = Just (notAssumedConstraint n ded (taun 1 :: FregeanDescSeq (Term Int)))
        globalRestriction _ _ _ = Nothing

        globalRestriction (Left ded) n (GNDP (CoreP InA))   = Just (notAssumedConstraint n ded (taun 1 :: FregeanDescSeq (Term Int)))
        globalRestriction (Left ded) n (GNDP (CoreP ElimE)) = Just (notAssumedConstraint n ded (taun 1 :: FregeanDescSeq (Term Int)))
        globalRestriction (Left ded) n (GNDP (NDP (PND (IPND (MPND InIf1))))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (GNDP (NDP (PND (IPND (MPND InIf2))))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (GNDP (NDP (PND (IPND (MPND InNeg1))))) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (GNDP (NDP (PND (IPND (MPND InNeg2))))) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

        isAssumption (GNDP x) = isAssumption x
        isAssumption _ = False

parseGamutNDDesc rtc = try ndRule
    where ndRule = map GNDP <$> parseGamutNDPlus (RuntimeNaturalDeductionConfig mempty mempty)

parseGamutNDDescProof :: RuntimeNaturalDeductionConfig FregeanDescLex (Form Bool) -> String -> [DeductionLine GamutNDDesc FregeanDescLex (Form Bool)]
parseGamutNDDescProof rtc = toDeductionFitch (parseGamutNDDesc rtc) (gamutNDDescFormulaParser)

gamutNDDescCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutNDDescProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gamutNDDescFormulaParser
    , ndParseForm = gamutNDDescFormulaParser
    , ndNotation = gamutNotation
    }

ofDefiniteDescSys :: (forall r sem lex . 
    SupportsND r (OpenLexiconFOL lex) sem => 
    NaturalDeductionCalc r (OpenLexiconFOL lex) sem -> a) -> String 
      -> Maybe a
ofDefiniteDescSys f sys 
        | sys == "gamutNDDesc"       = Just $ f gamutNDDescCalc
        | otherwise                  = Nothing
