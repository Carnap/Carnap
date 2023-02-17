{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureSecondOrder.Logic.Carnap (psolCalc, msolCalc) where

import Carnap.Core.Data.Types
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint)
import Carnap.Languages.PureFirstOrder.Logic (FOLogic(ED1,ED2,UD,UI,EG),parseFOLogic)
import Carnap.Languages.PureSecondOrder.Parser
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineMontague, hoProcessLineMontagueMemo)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Text.Parsec
import Carnap.Languages.PureSecondOrder.Logic.Rules

data MSOLogic = ABS | APP | SOUI | SOEG | SOUD | SOED1 | SOED2 | FO FOLogic 
                    | PR (Maybe [(ClassicalSequentOver MonadicallySOLLex (Sequent (Form Bool)))])
        deriving (Eq)

instance Show MSOLogic where
        show (PR _) = "PR"
        show ABS    = "ABS"
        show APP    = "APP"
        show SOUI   = "UI"
        show SOEG   = "EG"
        show SOUD   = "UD"
        show SOED1  = "ED"
        show SOED2  = "ED"
        show (FO x) = show x

somgamma :: Int -> ClassicalSequentOver MonadicallySOLLex (Antecedent (Form Bool))
somgamma = GammaV

instance Inference MSOLogic MonadicallySOLLex (Form Bool) where
        ruleOf (PR _) = [] ∴ SA (phin 1) :|-: SS (phin 1)
        ruleOf ABS    = monadicAbstraction
        ruleOf APP    = monadicApplication
        ruleOf SOUI   = monadicUniversalInstantiation
        ruleOf SOEG   = monadicExistentialGeneralization
        ruleOf SOUD   = monadicUniversalDerivation
        ruleOf SOED1  = monadicExistentialDerivation !! 0
        ruleOf SOED2  = monadicExistentialDerivation !! 1

        premisesOf (FO x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf (FO x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        restriction (PR prems) = Just (premConstraint prems)
        restriction SOUD = 
            Just (sopredicateEigenConstraint (liftToSequent $ SOMScheme 1) (ss (lall "v" (\x -> SOMCtx 1 :!$: x)))  (somgamma 1))
        restriction x | (x == SOED1) || (x == SOED2) = 
            Just (sopredicateEigenConstraint (liftToSequent $ SOMScheme 1) (ss (lsome "v" (\x -> SOMCtx 1 :!$: x)) :-: ss phiS) (somgamma 1 :+: somgamma 2))
        restriction (FO UD) = 
            Just (eigenConstraint stau (ss $ lall "v" phi) (somgamma 1))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent tau
        restriction x | (x == FO ED1) || (x == FO ED2) = 
            Just (eigenConstraint stau ((ss $ lsome "v" phi) :-: ss phiS) (somgamma 1 :+: somgamma 2))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent tau
        restriction _ = Nothing

        indirectInference (FO x) = indirectInference x
        indirectInference x
            | x `elem` [SOED1, SOED2, SOUD] = Just PolyProof
            | otherwise = Nothing

parseMSOLogic :: RuntimeDeductionConfig MonadicallySOLLex (Form Bool) 
                    -> Parsec String u [MSOLogic]
parseMSOLogic rtc = try soRule <|> liftFO
    where liftFO = do r <- parseFOLogic (defaultRuntimeDeductionConfig)
                      return (map FO r)
          soRule = do r <- choice (map (try . string) ["PR", "UI", "UD", "EG", "ED", "ABS","APP"])
                      case r of 
                            r | r == "PR"   -> return [PR $ problemPremises rtc]
                              | r == "UI"   -> return [FO UI, SOUI]
                              | r == "UD"   -> return [SOUD, FO UD]
                              | r == "EG"   -> return [FO EG, SOEG]
                              | r == "ED"   -> return [FO ED1,FO ED2, SOED1, SOED2]
                              | r == "ABS"  -> return [ABS]
                              | r == "APP"  -> return [APP]

parseMSOLProof :: RuntimeDeductionConfig MonadicallySOLLex (Form Bool) 
                    -> String -> [DeductionLine MSOLogic MonadicallySOLLex (Form Bool)]
parseMSOLProof rtc = toDeductionMontague (parseMSOLogic rtc) msolFormulaParser

msolCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseMSOLProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    }

-------------------------------------------

data PSOLogic = ABS_PSOL Int   | APP_PSOL Int 
              | SOUI_PSOL Int  | SOEG_PSOL Int 
              | SOUD_PSOL Int  | SOED1_PSOL Int 
              | SOED2_PSOL Int | FO_PSOL FOLogic
              | PPR (Maybe [(ClassicalSequentOver PolyadicallySOLLex (Sequent (Form Bool)))])
    deriving (Eq)

instance Show PSOLogic where
        show (PPR _)        = "PR"
        show (ABS_PSOL n)   = "ABS" ++ show n
        show (APP_PSOL n)   = "APP" ++ show n
        show (SOUI_PSOL n)  = "UI"  ++ show n
        show (SOEG_PSOL n)  = "EG"  ++ show n
        show (SOUD_PSOL n)  = "UD"  ++ show n
        show (SOED1_PSOL n) = "ED"  ++ show n
        show (SOED2_PSOL n) = "ED"  ++ show n
        show (FO_PSOL x) = show x

sogamma :: Int -> ClassicalSequentOver PolyadicallySOLLex (Antecedent (Form Bool))
sogamma = GammaV

instance Inference PSOLogic PolyadicallySOLLex (Form Bool) where
        ruleOf (PPR _) = [] ∴ SA (phin 1) :|-: SS (phin 1)
        ruleOf (ABS_PSOL n) = polyadicAbstraction n
        ruleOf (APP_PSOL n) = polyadicApplication n
        ruleOf (SOUI_PSOL n) = polyadicUniversalInstantiation n
        ruleOf (SOUD_PSOL n) = polyadicUniversalDerivation n
        ruleOf (SOEG_PSOL n)   = polyadicExistentialGeneralization n
        ruleOf (SOED1_PSOL n) = polyadicExistentialDerivation n !! 0
        ruleOf (SOED2_PSOL n) = polyadicExistentialDerivation n !! 1

        premisesOf (FO_PSOL x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf (FO_PSOL x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        restriction (PPR prems) = Just (premConstraint prems)

        restriction (SOUD_PSOL n)  = 
            Just (psopredicateEigenConstraint (liftToSequent $ psolAppScheme (n - 1)) (ss' $ universalScheme n)  (sogamma 1))
              -- XXX would be better to use
              -- contexts alone in line above
        restriction (SOED1_PSOL n) =
            Just (psopredicateEigenConstraint (liftToSequent $ psolAppScheme (n - 1)) (ss' $ existentialScheme n)  (sogamma 1 :+: sogamma 2))
        restriction (SOED2_PSOL n) = 
            Just (psopredicateEigenConstraint (liftToSequent $ psolAppScheme (n - 1)) (ss' $ existentialScheme n)  (sogamma 1 :+: sogamma 2))
        restriction (FO_PSOL UD)  = 
            Just (eigenConstraint stau (ss' $ lall "v" phi) (sogamma 1))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent taup
        restriction x | (x == FO_PSOL ED1) || (x == FO_PSOL ED2) = 
            Just (eigenConstraint stau ((ss' $ lsome "v" phi) :-: ss' phiSp) (sogamma 1 :+: sogamma 2))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  
                  stau = liftToSequent taup
        restriction _ = Nothing
        
        indirectInference (FO_PSOL x) = indirectInference x
        indirectInference (SOED1_PSOL _) = Just PolyProof 
        indirectInference (SOED2_PSOL _) = Just PolyProof 
        indirectInference (SOUD_PSOL _)  = Just PolyProof
        indirectInference _  = Nothing

parsePSOLogic :: RuntimeDeductionConfig PolyadicallySOLLex (Form Bool)
                    -> Parsec String u [PSOLogic]
parsePSOLogic rtc = try soRule <|> liftFO
    where liftFO = do r <- parseFOLogic (defaultRuntimeDeductionConfig)
                      return (map FO_PSOL r)
          soRule = do r <- choice (map (try . string) ["PR", "UI", "UD", "EG", "ED", "ABS","APP"])
                      if r == "PR" 
                          then return [PPR $ problemPremises rtc]
                          else do ds <- many1 digit
                                  let n = read ds :: Int
                                  case r of 
                                        r | r == "UI"   -> return [SOUI_PSOL n]
                                          | r == "UD"   -> return [SOUD_PSOL n]
                                          | r == "EG"   -> return [SOEG_PSOL n]
                                          | r == "ED"   -> return [SOED1_PSOL n, SOED2_PSOL n]
                                          | r == "ABS"  -> return [ABS_PSOL n]
                                          | r == "APP"  -> return [APP_PSOL n]

parsePSOLProof :: RuntimeDeductionConfig PolyadicallySOLLex (Form Bool) 
                    -> String -> [DeductionLine PSOLogic PolyadicallySOLLex (Form Bool)]
parsePSOLProof rtc = toDeductionMontague (parsePSOLogic rtc) psolFormulaParser

psolCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parsePSOLProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    }
