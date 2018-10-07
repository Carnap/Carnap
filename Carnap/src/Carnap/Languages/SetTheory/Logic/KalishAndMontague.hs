{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Logic.KalishAndMontague
        (estCalc)
    where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint)
import Carnap.Languages.PureFirstOrder.Logic (FOLogic(ED1,ED2,UD, UI, EG, UD, ED1, ED2, QN1, QN2, QN3, QN4, LL1, LL2, ALL1, ALL2, EL1, EL2, ID, SM, SL), parseFOLogic)
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.SetTheory.Parser
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineMontague, hoProcessLineMontagueMemo)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Text.Parsec
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.SetTheory.Logic.Rules
import Carnap.Languages.PureFirstOrder.Logic.Rules (phi, phi',eigenConstraint, tau)

data ESTLogic = DefU1 | DefI1 | DefP1 | DefC1
              | DefU2 | DefI2 | DefP2 | DefC2
              | FO FOLogic | PR (Maybe [(ClassicalSequentOver ElementarySetTheoryLex (Sequent (Form Bool)))])
              deriving (Eq)

instance Show ESTLogic where
        show (PR _)  = "PR"
        show (FO x)  = show x
        show DefU1   = "Def-U"
        show DefI1   = "Def-I"
        show DefC1   = "Def-C"
        show DefP1   = "Def-P"
        show DefU2   = "Def-U"
        show DefI2   = "Def-I"
        show DefC2   = "Def-C"
        show DefP2   = "Def-P"


instance Inference ESTLogic ElementarySetTheoryLex (Form Bool) where
     ruleOf (PR _)    = axiom
     ruleOf DefU1     = unpackUnion !! 0 
     ruleOf DefI1     = unpackIntersection !! 0
     ruleOf DefP1     = unpackPowerset !! 0
     ruleOf DefC1     = unpackComplement !! 0
     ruleOf DefU2     = unpackUnion !! 1 
     ruleOf DefI2     = unpackIntersection !! 1
     ruleOf DefP2     = unpackPowerset !! 1
     ruleOf DefC2     = unpackComplement !! 1
     ruleOf (FO UI  ) = universalInstantiation
     ruleOf (FO EG  ) = existentialGeneralization
     ruleOf (FO UD  ) = universalGeneralization
     ruleOf (FO ED1 ) = existentialDerivation !! 0
     ruleOf (FO ED2 ) = existentialDerivation !! 1
     ruleOf (FO QN1 ) = quantifierNegation !! 0
     ruleOf (FO QN2 ) = quantifierNegation !! 1
     ruleOf (FO QN3 ) = quantifierNegation !! 2
     ruleOf (FO QN4 ) = quantifierNegation !! 3
     ruleOf (FO LL1 ) = leibnizLawVariations !! 0
     ruleOf (FO LL2 ) = leibnizLawVariations !! 1
     ruleOf (FO ALL1) = antiLeibnizLawVariations !! 0
     ruleOf (FO ALL2) = antiLeibnizLawVariations !! 1
     ruleOf (FO EL1 ) = euclidsLawVariations !! 0
     ruleOf (FO EL2 ) = euclidsLawVariations !! 1
     ruleOf (FO ID  ) = eqReflexivity
     ruleOf (FO SM  ) = eqSymmetry

     premisesOf (FO (SL x)) = map liftSequent (premisesOf x)
     premisesOf r = upperSequents (ruleOf r)

     conclusionOf (FO (SL x)) = liftSequent (conclusionOf x)
     conclusionOf r = lowerSequent (ruleOf r)

     restriction (PR prems) = Just (premConstraint prems)
     restriction (FO UD)    = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (setgamma 1))
         where stau = liftToSequent tau
               setgamma :: Int -> ClassicalSequentOver ElementarySetTheoryLex (Antecedent (Form Bool))
               setgamma = GammaV

     restriction (FO ED1)   = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (setgamma 1 :+: setgamma 2))
         where stau = liftToSequent tau
               setgamma :: Int -> ClassicalSequentOver ElementarySetTheoryLex (Antecedent (Form Bool))
               setgamma = GammaV
     restriction _ = Nothing

     indirectInference (FO x) = indirectInference x
     indirectInference _ = Nothing

parseESTLogic :: RuntimeNaturalDeductionConfig ElementarySetTheoryLex (Form Bool) -> Parsec String u [ESTLogic]
parseESTLogic rtc = try estRule <|> liftFO
    where liftFO = do r <- parseFOLogic (RuntimeNaturalDeductionConfig mempty mempty)
                      return (map FO r)
          estRule = do r <- choice (map (try . string) ["PR", "Def-U", "Def-I", "Def-C", "Def-P"])
                       case r of 
                            r | r == "PR"    -> return [PR $ problemPremises rtc]
                              | r == "Def-U" -> return [DefU1, DefU2]
                              | r == "Def-I" -> return [DefI1, DefI2]
                              | r == "Def-C" -> return [DefC1, DefC2]
                              | r == "Def P" -> return [DefP1, DefP2]

parseESTProof:: RuntimeNaturalDeductionConfig ElementarySetTheoryLex (Form Bool) 
                    -> String -> [DeductionLine ESTLogic ElementarySetTheoryLex (Form Bool)]
parseESTProof rtc = toDeductionMontague (parseESTLogic rtc) elementarySetTheoryParser

estCalc = NaturalDeductionCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseESTProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    , ndParseSeq = seqFormulaParser
    }
