{-#LANGUAGE  FlexibleContexts, RankNTypes, FlexibleInstances, MultiParamTypeClasses, TypeOperators #-}
module Carnap.Languages.DefiniteDescription.Logic.Gamut (gamutNDDescCalc, parseGamutNDDesc, ofDefiniteDescSys) where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.DefiniteDescription.Syntax
import Carnap.Languages.DefiniteDescription.Parser
import Carnap.Languages.PurePropositional.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Syntax (fogamma, PureLexiconFOL)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (fitchAssumptionCheck)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Text.Parsec

data GamutNDDesc = GNDP GamutNDPlus | InDD1 | InDD2 | ElimDD1 | ElimDD2 | EqS
    deriving Eq

instance Show GamutNDDesc where
        show (GNDP x) = show x
        show InDD1 = "I℩"
        show InDD2 = "I℩"
        show ElimDD1 = "E℩"
        show ElimDD2 = "E℩"
        show EqS = "S="

instance Inference GamutNDDesc FregeanDescLex (Form Bool) where
        ruleOf InDD1 = [GammaV 1 :|-: SS (lsome "v" $ \x -> phi' 1 x ./\. (lall "w" $ \y -> phi' 1 y .=>. (y `equals` x)))
                       ] ∴ GammaV 1 :|-: SS (phi 1 (ddesc "v" (phi' 1)))
        ruleOf InDD2 = [GammaV 1 :|-: SS (lsome "v" $ \x -> phi' 1 x ./\. (lall "w" $ \y -> phi' 1 y .=>. (x `equals` y)))
                       ] ∴ GammaV 1 :|-: SS (phi 1 (ddesc "v" (phi' 1)))
        ruleOf ElimDD1 = [GammaV 1 :|-: SS (lneg $ ddesc "v" (phi' 1) `equals` ddesc "v" (\x -> (lfalsum :: FregeanDescSeq (Form Bool))))
                         ] ∴ GammaV 1 :|-: SS (lsome "v" $ \x -> phi' 1 x ./\. (lall "w" $ \y -> phi' 1 y .=>. (y `equals` x)))
        ruleOf ElimDD2 = [GammaV 1 :|-: SS (lneg $ ddesc "v" (phi' 1) `equals` ddesc "v" (\x -> (lfalsum :: FregeanDescSeq (Form Bool))))
                         ] ∴ GammaV 1 :|-: SS (lsome "v" $ \x -> phi' 1 x ./\. (lall "w" $ \y -> phi' 1 y .=>. (x `equals` y)))
        ruleOf EqS = eqSymmetryReplacement !! 0
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

parseGamutNDDesc rtc = try ndRule <|> descRule
    where ndRule = map GNDP <$> parseGamutNDPlus (defaultRuntimeDeductionConfig)
          descRule = do r <- choice (map (try . string) ["Ii","Ei", "S="])
                        return $ case r of
                            "Ii" -> [InDD1, InDD2]
                            "Ei" -> [ElimDD1, ElimDD2]
                            "S=" -> [EqS]

parseGamutNDDescProof :: RuntimeDeductionConfig FregeanDescLex (Form Bool) -> String -> [DeductionLine GamutNDDesc FregeanDescLex (Form Bool)]
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

ofDefiniteDescSys :: (forall r .  ( Inference r FregeanDescLex (Form Bool), Show r) => 
    NaturalDeductionCalc r FregeanDescLex (Form Bool) -> a) -> String -> Maybe a
ofDefiniteDescSys f sys 
        | sys == "gamutNDDesc"       = Just $ f gamutNDDescCalc
        | otherwise                  = Nothing
