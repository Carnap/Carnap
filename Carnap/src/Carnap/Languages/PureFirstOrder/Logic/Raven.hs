{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Raven 
    ( ravenFOLCoreCalc, ravenFOLCalc, parseRavenFOL, RavenFOL
    , ravenFOL2019Calc, parseRavenFOLCore, RavenFOLCore
    , ravenFOLPlus2019Calc
    ) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form, Term)
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
import qualified Carnap.Languages.PurePropositional.Logic.Raven as TFL
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint, fitchAssumptionCheck, axiom)

--------------------
--  3. System FOL  --
--------------------
-- A system of first-order logic resembling system FOL from the Calcary
-- Remix of forall x

data RavenFOLCore = TFLC P.RavenTFLCore | UI | UE | EI | EE1 | EE2 | IDI | IDE1 | IDE2 
                            | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                    deriving Eq

data RavenFOL = TFL P.RavenTFL | FOL RavenFOLCore | QN1 | QN2 | QN3 | QN4

instance Show RavenFOLCore where
        show (TFLC x) = show x
        show UI          = "∀I"
        show UE          = "∀E"
        show EI          = "∃I"
        show EE1         = "∃E"
        show EE2         = "∃E"
        show IDI         = "=I"
        show IDE1        = "=E"
        show IDE2        = "=E"
        show (Pr _)      = "PR"

instance Show RavenFOL where
        show (TFL x)     = show x
        show (FOL x)     = show x
        show QN1         = "CQ"
        show QN2         = "CQ"
        show QN3         = "CQ"
        show QN4         = "CQ"

instance Inference RavenFOLCore PureLexiconFOL (Form Bool) where

         ruleOf r@(TFLC _) = premisesOf r ∴ conclusionOf r
         ruleOf UI     = universalGeneralization
         ruleOf UE     = universalInstantiation
         ruleOf EI     = existentialGeneralization
         ruleOf EE1    = existentialDerivation !! 0 
         ruleOf EE2    = existentialDerivation !! 1 
         ruleOf IDI    = eqReflexivity
         ruleOf (Pr _) = axiom
         ruleOf IDE1  = leibnizLawVariations !! 0
         ruleOf IDE2  = leibnizLawVariations !! 1

         premisesOf (TFLC x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)

         conclusionOf (TFLC x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (TFLC x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI    = Just (eigenConstraint tau (SS $ lall "v" $ phi' 1) (fogamma 1))
         restriction EE1   = Just (eigenConstraint tau ((SS $ lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2   = Just (eigenConstraint tau ((SS $ lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _     = Nothing

         globalRestriction (Left ded) n (TFLC TFL.CondIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (TFLC TFL.CondIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (TFLC TFL.BicoIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFLC TFL.BicoIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFLC TFL.BicoIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFLC TFL.BicoIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFLC TFL.DisjElim1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFLC TFL.DisjElim2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFLC TFL.DisjElim3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFLC TFL.DisjElim4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFLC TFL.NegeIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (TFLC TFL.NegeIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (TFLC TFL.Indirect1) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction (Left ded) n (TFLC TFL.Indirect2) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction (Left ded) n UI = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
         globalRestriction (Left ded) n r | r `elem` [EE1,EE2] = 
            case dependencies (ded !! (n - 1)) of
              Just ls -> firstDistinct ls
              Nothing -> Nothing
            where firstDistinct [] = Nothing
                  firstDistinct ((a,b):xs) | a /= b = Just (notAssumedConstraint a ded (taun 1 :: FOLSequentCalc (Term Int)))
                                           | otherwise = firstDistinct xs
         globalRestriction _ _ _ = Nothing

         isAssumption (TFLC x) = isAssumption x
         isAssumption _ = False

         isPremise (Pr _) = True
         isPremise _ = False

instance Inference RavenFOL PureLexiconFOL (Form Bool) where

         ruleOf (FOL x) = ruleOf x
         ruleOf r@(TFL _) = premisesOf r ∴ conclusionOf r
         ruleOf QN1    = quantifierNegation !! 0 
         ruleOf QN2    = quantifierNegation !! 1
         ruleOf QN3    = quantifierNegation !! 2
         ruleOf QN4    = quantifierNegation !! 3

         premisesOf (TFL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)

         conclusionOf (TFL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (TFL x) = indirectInference x
         indirectInference (FOL x) = indirectInference x
         indirectInference _ = Nothing

         restriction (FOL x) = restriction x
         restriction _       = Nothing

         globalRestriction (Left ded) n (TFL (TFL.Core TFL.CondIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.CondIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.BicoIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.BicoIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.BicoIntro3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.BicoIntro4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.DisjElim1))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.DisjElim2))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.DisjElim3))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.DisjElim4))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.NegeIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.NegeIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.Indirect1))  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction (Left ded) n (TFL (TFL.Core TFL.Indirect2))  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
         globalRestriction (Left ded) n (FOL UI) = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
         globalRestriction _ _ _ = Nothing

         isAssumption (TFL x) = isAssumption x
         isAssumption (FOL x) = isAssumption x
         isAssumption _ = False

         isPremise (FOL x) = isPremise x
         isPremise _ = False

parseRavenFOLCore rtc = try quantRule <|> (map TFLC <$> parseProp)
    where parseProp = P.parseRavenTFLCore (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["∀I", "@I", "AI", "∀E", "@E", "AE", "∃I", "3I", "EI", "3E", "∃E", "EE", "=I","=E","PR"])
                         case r of 
                            r | r `elem` ["∀I","@I","AI"] -> return [UI]
                              | r `elem` ["∀E","@E","AE"] -> return [UE]
                              | r `elem` ["∃I","3I","EI"] -> return [EI]
                              | r `elem` ["∃E","3E","EE"] -> return [EE1, EE2]
                              | r == "=I" -> return [IDI]
                              | r == "=E" -> return [IDE1,IDE2]
                              | r == "PR" -> return [Pr (problemPremises rtc)]

--XXX ordering of the parsing clauses is important here: TFLCore is included
--in FOLCore, and in TFL, we want to get the version that is including in
--TFL, so that our global restrictions will apply properly
parseRavenFOL rtc = try premRule <|> try (map TFL <$> parseProp) <|> try (map FOL <$> quantRule) <|>  try cqRule
    where parseProp = P.parseRavenTFL (defaultRuntimeDeductionConfig)
          quantRule = parseRavenFOLCore rtc
          cqRule = string "CQ" >> return [QN1,QN2,QN3,QN4]
          premRule = string "PR" >> return [FOL $ Pr (problemPremises rtc)] --short-circuit TFL from handling premises

parseRavenFOL2019Proof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine RavenFOLCore PureLexiconFOL (Form Bool)]
parseRavenFOL2019Proof ders = toDeductionFitch (parseRavenFOLCore ders) thomasBolducAndZachFOL2019FormulaParser

parseRavenFOLPlus2019Proof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine RavenFOL PureLexiconFOL (Form Bool)]
parseRavenFOLPlus2019Proof ders = toDeductionFitch (parseRavenFOL ders) thomasBolducAndZachFOL2019FormulaParser

parseRavenFOLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine RavenFOL PureLexiconFOL (Form Bool)]
parseRavenFOLProof ders = toDeductionFitch (parseRavenFOL ders) thomasBolducAndZachFOLFormulaParser

parseRavenFOLCoreProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine RavenFOLCore PureLexiconFOL (Form Bool)]
parseRavenFOLCoreProof ders = toDeductionFitch (parseRavenFOLCore ders) thomasBolducAndZachFOLFormulaParser

ravenFOLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseRavenFOLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOLFormulaParser
    , ndParseForm = thomasBolducAndZachFOLFormulaParser
    , ndNotation = ndNotation P.ravenTFLCalc
    }

ravenFOLCoreCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseRavenFOLCoreProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOLFormulaParser
    , ndParseForm = thomasBolducAndZachFOLFormulaParser
    , ndNotation = ndNotation P.ravenTFLCalc
    }

ravenFOL2019Calc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseRavenFOL2019Proof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOL2019FormulaParser
    , ndParseForm = thomasBolducAndZachFOL2019FormulaParser
    , ndNotation = ndNotation P.ravenTFL2019Calc
    }

ravenFOLPlus2019Calc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseRavenFOLPlus2019Proof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOL2019FormulaParser
    , ndParseForm = thomasBolducAndZachFOL2019FormulaParser
    , ndNotation = ndNotation P.ravenTFL2019Calc
    }
