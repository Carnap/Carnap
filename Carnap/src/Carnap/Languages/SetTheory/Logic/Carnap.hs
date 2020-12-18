{-#LANGUAGE RankNTypes, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Logic.Carnap (estCalc, sstCalc) where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Syntax (fogamma)
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

data ESTLogic = DefU1   | DefI1 | DefP1 | DefC1 | DefC3 | DefID1 | DefID3 | DefSub1
              | DefU2   | DefI2 | DefP2 | DefC2 | DefC4 | DefID2 | DefID4 | DefSub2
              | FO FOLogic | PR (Maybe [(ClassicalSequentOver ElementarySetTheoryLex (Sequent (Form Bool)))])
              | Eq
              deriving (Eq)

instance Show ESTLogic where
        show (PR _)  = "PR"
        show (FO x)  = show x
        show DefU1   = "Def-U"
        show DefU2   = "Def-U"
        show DefI1   = "Def-I"
        show DefI2   = "Def-I"
        show DefC1   = "Def-C"
        show DefC2   = "Def-C"
        show DefC3   = "Def-C"
        show DefC4   = "Def-C"
        show DefID1  = "Def-="
        show DefID2  = "Def-="
        show DefID3  = "Def-="
        show DefID4  = "Def-="
        show DefP1   = "Def-P"
        show DefP2   = "Def-P"
        show DefSub1 = "Def-S"
        show DefSub2 = "Def-S"

instance Inference ESTLogic ElementarySetTheoryLex (Form Bool) where
     ruleOf (PR _)    = axiom
     ruleOf DefU1     = unpackUnion !! 0 
     ruleOf DefU2     = unpackUnion !! 1 
     ruleOf DefI1     = unpackIntersection !! 0
     ruleOf DefI2     = unpackIntersection !! 1
     ruleOf DefC1     = unpackComplement !! 0
     ruleOf DefC2     = unpackComplement !! 1
     ruleOf DefC3     = unpackComplement !! 2
     ruleOf DefC4     = unpackComplement !! 3
     ruleOf DefID1    = unpackEquality !! 0
     ruleOf DefID2    = unpackEquality !! 1
     ruleOf DefID3    = unpackEquality !! 2
     ruleOf DefID4    = unpackEquality !! 3
     ruleOf DefSub1   = unpackSubset !! 0
     ruleOf DefSub2   = unpackSubset !! 1
     ruleOf DefP1     = unpackPowerset !! 0
     ruleOf DefP2     = unpackPowerset !! 1
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
     restriction (FO UD)    = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1))
         where stau = liftToSequent tau

     restriction (FO ED1)   = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         where stau = liftToSequent tau
     restriction (FO ED2)   = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         where stau = liftToSequent tau
     restriction _ = Nothing

     indirectInference (FO x) = indirectInference x
     indirectInference _ = Nothing

parseESTLogic :: RuntimeNaturalDeductionConfig ElementarySetTheoryLex (Form Bool) -> Parsec String u [ESTLogic]
parseESTLogic rtc = try estRule <|> liftFO
    where liftFO = do r <- parseFOLogic (RuntimeNaturalDeductionConfig mempty mempty)
                      return (map FO r)
          estRule = do r <- choice (map (try . string) ["PR", "Def-U", "Def-I", "Def-C", "Def-P", "Def-S", "Def-="])
                       case r of 
                            r | r == "PR"    -> return [PR $ problemPremises rtc]
                              | r == "Def-U" -> return [DefU1, DefU2]
                              | r == "Def-I" -> return [DefI1, DefI2]
                              | r == "Def-C" -> return [DefC1, DefC2, DefC3, DefC4]
                              | r == "Def-S" -> return [DefSub1, DefSub2]
                              | r == "Def-P" -> return [DefP1, DefP2]
                              | r == "Def-=" -> return [DefID1, DefID2,DefID3,DefID4]

parseESTProof:: RuntimeNaturalDeductionConfig ElementarySetTheoryLex (Form Bool) 
                    -> String -> [DeductionLine ESTLogic ElementarySetTheoryLex (Form Bool)]
parseESTProof rtc = toDeductionMontague (parseESTLogic rtc) elementarySetTheoryParser

estCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseESTProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    }

data SSTLogic = EST ESTLogic | DefSep1 | DefSep2 | DefSep3 | DefSep4
         | PRS (Maybe [(ClassicalSequentOver SeparativeSetTheoryLex (Sequent (Form Bool)))])

instance Show SSTLogic where 
        show (PRS _)   = "PR"
        show DefSep1 = "Def-{}"
        show DefSep2 = "Def-{}"
        show DefSep3 = "Def-{}"
        show DefSep4 = "Def-{}"
        show (EST x) = show x

instance Inference SSTLogic SeparativeSetTheoryLex (Form Bool) where
     ruleOf (PRS _)          = axiom
     ruleOf DefSep1          = unpackSeparation !! 0
     ruleOf DefSep2          = unpackSeparation !! 1
     ruleOf DefSep3          = unpackSeparation !! 2
     ruleOf DefSep4          = unpackSeparation !! 3
     ruleOf (EST DefU1   )   = unpackUnion !! 0 
     ruleOf (EST DefU2   )   = unpackUnion !! 1 
     ruleOf (EST DefI1   )   = unpackIntersection !! 0
     ruleOf (EST DefI2   )   = unpackIntersection !! 1
     ruleOf (EST DefC1   )   = unpackComplement !! 0
     ruleOf (EST DefC2   )   = unpackComplement !! 1
     ruleOf (EST DefC3   )   = unpackComplement !! 2
     ruleOf (EST DefC4   )   = unpackComplement !! 3
     ruleOf (EST DefID1  )   = unpackEquality !! 0
     ruleOf (EST DefID2  )   = unpackEquality !! 1
     ruleOf (EST DefID3  )   = unpackEquality !! 2
     ruleOf (EST DefID4  )   = unpackEquality !! 3
     ruleOf (EST DefP1   )   = unpackPowerset !! 0
     ruleOf (EST DefP2   )   = unpackPowerset !! 1
     ruleOf (EST DefSub1 )   = unpackSubset !! 0
     ruleOf (EST DefSub2 )   = unpackSubset !! 1
     ruleOf (EST (FO UI  ))  = universalInstantiation
     ruleOf (EST (FO EG  ))  = existentialGeneralization
     ruleOf (EST (FO UD  ))  = universalGeneralization
     ruleOf (EST (FO ED1 ))  = existentialDerivation !! 0
     ruleOf (EST (FO ED2 ))  = existentialDerivation !! 1
     ruleOf (EST (FO QN1 ))  = quantifierNegation !! 0
     ruleOf (EST (FO QN2 ))  = quantifierNegation !! 1
     ruleOf (EST (FO QN3 ))  = quantifierNegation !! 2
     ruleOf (EST (FO QN4 ))  = quantifierNegation !! 3
     ruleOf (EST (FO LL1 ))  = leibnizLawVariations !! 0
     ruleOf (EST (FO LL2 ))  = leibnizLawVariations !! 1
     ruleOf (EST (FO ALL1))  = antiLeibnizLawVariations !! 0
     ruleOf (EST (FO ALL2))  = antiLeibnizLawVariations !! 1
     ruleOf (EST (FO EL1 ))  = euclidsLawVariations !! 0
     ruleOf (EST (FO EL2 ))  = euclidsLawVariations !! 1
     ruleOf (EST (FO ID  ))  = eqReflexivity
     ruleOf (EST (FO SM  ))  = eqSymmetry

     premisesOf (EST (FO (SL x))) = map liftSequent (premisesOf x)
     premisesOf r = upperSequents (ruleOf r)

     conclusionOf (EST (FO (SL x))) = liftSequent (conclusionOf x)
     conclusionOf r = lowerSequent (ruleOf r)

     restriction (PRS prems) = Just (premConstraint prems)
     restriction (EST (FO UD))    = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1))
         where stau = liftToSequent tau
     restriction (EST (FO ED1))   = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         where stau = liftToSequent tau
     restriction (EST (FO ED2))   = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         where stau = liftToSequent tau
     restriction _ = Nothing

     indirectInference (EST (FO x)) = indirectInference x
     indirectInference _ = Nothing

parseSSTLogic :: RuntimeNaturalDeductionConfig SeparativeSetTheoryLex (Form Bool) -> Parsec String u [SSTLogic]
parseSSTLogic rtc = try sepRule <|> liftEST
    where liftEST = do r <- parseESTLogic (RuntimeNaturalDeductionConfig mempty mempty)
                       return (map EST r)
          sepRule = do r <- choice (map (try . string) ["PR", "Def-{}"])
                       case r of 
                            r | r == "PR"    -> return [PRS $ problemPremises rtc]
                              | r == "Def-{}" -> return [DefSep1, DefSep2, DefSep3, DefSep4]

parseSSTProof:: RuntimeNaturalDeductionConfig SeparativeSetTheoryLex (Form Bool) 
                    -> String -> [DeductionLine SSTLogic SeparativeSetTheoryLex (Form Bool)]
parseSSTProof rtc = toDeductionMontague (parseSSTLogic rtc) separativeSetTheoryParser

sstCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseSSTProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    }
