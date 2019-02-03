{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.ThomasBolducAndZach (thomasBolducAndZachFOLCalc,parseThomasBolducAndZachFOL) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

--------------------
--  3. System FOL  --
--------------------
-- A system of first-order logic resembling system FOL from the Calcary
-- Remix of forall x

data ThomasBolducAndZachFOL = ThomasBolducAndZachTFL P.ThomasBolducAndZachTFL | UI | UE | EI | EE1 | EE2 | IDI | IDE1 | IDE2 | QN1 | QN2 | QN3 | QN4
                            | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                    deriving Eq

instance Show ThomasBolducAndZachFOL where
        show (ThomasBolducAndZachTFL x) = show x
        show UI          = "∀I"
        show UE          = "∀E"
        show EI          = "∃I"
        show EE1         = "∃E"
        show EE2         = "∃E"
        show IDI         = "=I"
        show IDE1        = "=E"
        show IDE2        = "=E"
        show QN1         = "CQ"
        show QN2         = "CQ"
        show QN3         = "CQ"
        show QN4         = "CQ"
        show (Pr _)      = "PR"

instance Inference ThomasBolducAndZachFOL PureLexiconFOL (Form Bool) where

         ruleOf UI     = universalGeneralization
         ruleOf UE     = universalInstantiation
         ruleOf EI     = existentialGeneralization
         ruleOf EE1    = existentialDerivation !! 0 
         ruleOf EE2    = existentialDerivation !! 1 
         ruleOf IDI    = eqReflexivity
         ruleOf QN1    = quantifierNegation !! 0 
         ruleOf QN2    = quantifierNegation !! 1
         ruleOf QN3    = quantifierNegation !! 2
         ruleOf QN4    = quantifierNegation !! 3
         ruleOf (Pr _) = axiom

         ruleOf IDE1  = leibnizLawVariations !! 0
         ruleOf IDE2  = leibnizLawVariations !! 1

         premisesOf (ThomasBolducAndZachTFL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (ThomasBolducAndZachTFL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (ThomasBolducAndZachTFL x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI    = Just (eigenConstraint (SeqT 1) (SS $ lall "v" $ phi' 1) (fogamma 1))
         restriction EE1   = Just (eigenConstraint (SeqT 1) ((SS $ lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2   = Nothing --Since this one does not use the assumption with a fresh object
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _     = Nothing

         isAssumption (ThomasBolducAndZachTFL x) = isAssumption x
         isAssumption _ = False

         isPremise (Pr _) = True
         isPremise _ = False

parseThomasBolducAndZachFOL rtc = try quantRule <|> liftProp
    where liftProp = do r <- P.parseThomasBolducAndZachTFL (RuntimeNaturalDeductionConfig mempty mempty)
                        return (map ThomasBolducAndZachTFL r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E","CQ","PR"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r == "=I" -> return [IDI]
                              | r == "=E" -> return [IDE1,IDE2]
                              | r == "CQ" -> return [QN1,QN2,QN3,QN4]
                              | r == "PR" -> return [Pr (problemPremises rtc)]

parseThomasBolducAndZachFOLProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine ThomasBolducAndZachFOL PureLexiconFOL (Form Bool)]
parseThomasBolducAndZachFOLProof ders = toDeductionFitch (parseThomasBolducAndZachFOL ders) thomasBolducAndZachFOLFormulaParser

thomasBolducAndZachFOLCalc = mkNDCalc
    { ndRenderer = FitchStyle
    , ndParseProof = parseThomasBolducAndZachFOLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOLFormulaParser
    , ndNotation = ndNotation P.thomasBolducAndZachTFLCalc
    }
