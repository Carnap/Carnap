{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gallow
    ( gallowPLCalc, gallowPLPlusCalc ) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import qualified Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach as TFL
import Carnap.Languages.PurePropositional.Logic.Gallow
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint, fitchAssumptionCheck, axiom)

--------------------
--  3. System FOL  --
--------------------
-- A system of first-order logic resembling system FOL from the Calcary
-- Remix of forall x

data GallowPLCore = SLCore GallowSLCore | UI | UE | EI | EE1 | EE2
                    | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                    deriving Eq

data GallowPL = SL GallowSL | PL GallowPLCore | QN1 | QN2 | QN3 | QN4
              deriving Eq

instance Show GallowPLCore where
        show (SLCore x) = show x
        show UI          = "∀I"
        show UE          = "∀E"
        show EI          = "∃I"
        show EE1         = "∃E"
        show EE2         = "∃E"
        show (Pr _)      = "PR"

instance Show GallowPL where
        show (SL x)     = show x
        show (PL x)     = show x
        show QN1         = "CQ"
        show QN2         = "CQ"
        show QN3         = "CQ"
        show QN4         = "CQ"

instance Inference GallowPLCore PureLexiconFOL (Form Bool) where

         ruleOf r@(SLCore _) = premisesOf r ∴ conclusionOf r
         ruleOf UI     = universalGeneralization
         ruleOf UE     = universalInstantiation
         ruleOf EI     = existentialGeneralization
         ruleOf EE1    = existentialDerivation !! 0 
         ruleOf EE2    = existentialDerivation !! 1 
         ruleOf (Pr _) = axiom

         premisesOf (SLCore x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (SLCore x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (SLCore x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI    = Just (eigenConstraint tau (SS $ lall "v" $ phi' 1) (fogamma 1))
         restriction EE1   = Just (eigenConstraint tau ((SS $ lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2   = Just (eigenConstraint tau ((SS $ lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _     = Nothing
         
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.CondIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.CondIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.BicoIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.BicoIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.BicoIntro3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.BicoIntro4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.DisjElim1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.DisjElim2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.DisjElim3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.DisjElim4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.NegeIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.NegeIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.Indirect1)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction (Left ded) n (SLCore (GallowSLCore TFL.Indirect2)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction _ _ _ = Nothing

         isAssumption (SLCore x) = isAssumption x
         isAssumption _ = False

         isPremise (Pr _) = True
         isPremise _ = False

instance Inference GallowPL PureLexiconFOL (Form Bool) where

         ruleOf (PL x) = ruleOf x
         ruleOf r@(SL _) = premisesOf r ∴ conclusionOf r
         ruleOf QN1    = quantifierNegation !! 0 
         ruleOf QN2    = quantifierNegation !! 1
         ruleOf QN3    = quantifierNegation !! 2
         ruleOf QN4    = quantifierNegation !! 3

         premisesOf (SL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (SL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (SL x) = indirectInference x
         indirectInference (PL x) = indirectInference x
         indirectInference _ = Nothing

         restriction (PL x) = restriction x
         restriction _       = Nothing

         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.CondIntro1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.CondIntro2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.BicoIntro1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.BicoIntro2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.BicoIntro3))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.BicoIntro4))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.DisjElim1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.DisjElim2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.DisjElim3))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.DisjElim4))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.NegeIntro1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.NegeIntro2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.Indirect1))) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction (Left ded) n (PL (SLCore (GallowSLCore TFL.Indirect2))) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction _ _ _ = Nothing

         isAssumption (PL x) = isAssumption x
         isAssumption (SL x) = isAssumption x
         isAssumption _ = False

         isPremise (SL x) = isPremise x
         isPremise (PL x) = isPremise x
         isPremise _ = False

parseGallowPLCore rtc = try quantRule <|> (map SLCore <$> parseProp)
    where parseProp = parseGallowSLCore (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "PR"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r == "PR" -> return [Pr (problemPremises rtc)]

parseGallowPL rtc = try (map PL <$> quantRule) <|> try (map SL <$> parseProp) <|> try cqRule
    where parseProp = parseGallowSL (defaultRuntimeDeductionConfig)
          quantRule = parseGallowPLCore rtc
          cqRule = string "CQ" >> return [QN1,QN2,QN3,QN4]

parseGallowPLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GallowPLCore PureLexiconFOL (Form Bool)]
parseGallowPLProof ders = toDeductionFitch (parseGallowPLCore ders) gallowPLFormulaParser

parseGallowPLPlusProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GallowPL PureLexiconFOL (Form Bool)]
parseGallowPLPlusProof ders = toDeductionFitch (parseGallowPL ders) gallowPLFormulaParser

gallowPLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseGallowPLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gallowPLFormulaParser
    , ndParseForm = gallowPLFormulaParser
    , ndNotation = ndNotation P.thomasBolducAndZachTFLCalc
    }

gallowPLPlusCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseGallowPLPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gallowPLFormulaParser
    , ndParseForm = gallowPLFormulaParser
    , ndNotation = ndNotation P.thomasBolducAndZachTFLCalc
    }
