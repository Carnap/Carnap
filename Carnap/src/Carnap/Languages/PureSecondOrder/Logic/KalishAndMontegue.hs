
{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureSecondOrder.Logic.KalishAndMontegue (psolCalc, msolCalc) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConnectives
import Carnap.Languages.PureFirstOrder.Logic (FOLogic(..),parseFOLogic)
import Carnap.Languages.PureSecondOrder.Parser
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineMontegue, hoProcessLineMontegueMemo)
import Data.Map (empty)
import Text.Parsec
import Carnap.Languages.PureSecondOrder.Logic.Rules

data MSOLogic = ABS | APP | SOUI | SOEG | SOUD | SOED1 | SOED2 | FO FOLogic

instance Show MSOLogic where
        show ABS    = "ABS"
        show APP    = "APP"
        show SOUI   = "UI"
        show SOEG   = "EG"
        show SOUD   = "UD"
        show SOED1  = "ED"
        show SOED2  = "ED"
        show (FO x) = show x

instance Inference MSOLogic MonadicallySOLLex where
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

        restriction SOUD     = Just (sopredicateEigenConstraint 
                                        (liftToSequent $ SOMScheme 1) 
                                        (ss (SOMBind (SOAll "v") (\x -> SOMCtx 1 :!$: x)))  
                                        (GammaV 1))

        restriction SOED1    = Just (sopredicateEigenConstraint
                                        (liftToSequent $ SOMScheme 1)
                                        (ss (SOMBind (SOSome "v") (\x -> SOMCtx 1 :!$: x))
                                            :-: ss phiS)
                                        (GammaV 1 :+: GammaV 2))
        restriction (FO UD)  = Just (eigenConstraint stau 
                                        (ss $ SOBind (All "v") phi) 
                                        (GammaV 1))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent tau

        restriction (FO ED1) = Just (eigenConstraint stau 
                                        ((ss $ SOBind (Some "v") phi) :-: ss phiS) 
                                        (GammaV 1 :+: GammaV 2))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  
                  stau = liftToSequent tau
        restriction _ = Nothing

-- XXX Skipping derived rules for now.
parseMSOLogic :: Parsec String u [MSOLogic]
parseMSOLogic = try soRule <|> liftFO
    where liftFO = do r <- parseFOLogic empty
                      return (map FO r)
          soRule = do r <- choice (map (try . string) [ "UI", "UD", "EG", "ED", "ABS","APP"])
                      case r of 
                            r | r == "UI"   -> return [FO UI, SOUI]
                              | r == "UD"   -> return [SOUD, FO UD]
                              | r == "EG"   -> return [FO EG, SOEG]
                              | r == "ED"   -> return [FO ED1,FO ED2, SOED1, SOED2]
                              | r == "ABS"  -> return [ABS]
                              | r == "APP"  -> return [APP]

parseMSOLProof :: String -> [DeductionLine MSOLogic MonadicallySOLLex (Form Bool)]
parseMSOLProof = toDeductionMontegue parseMSOLogic msolFormulaParser

msolSeqParser = seqFormulaParser :: Parsec String () (MSOLSequentCalc Sequent)

msolCalc = NaturalDeductionCalc 
    { ndRenderer = MontegueStyle
    , ndParseProof = const parseMSOLProof -- XXX ignore derived rules for now
    , ndProcessLine = hoProcessLineMontegue
    , ndProcessLineMemo = Just hoProcessLineMontegueMemo
    , ndParseSeq = msolSeqParser
    }

-------------------------------------------

data PSOLogic = ABS_PSOL Int   | APP_PSOL Int 
              | SOUI_PSOL Int  | SOEG_PSOL Int 
              | SOUD_PSOL Int  | SOED1_PSOL Int 
              | SOED2_PSOL Int | FO_PSOL FOLogic

instance Show PSOLogic where
        show (ABS_PSOL n)   = "ABS" ++ show n
        show (APP_PSOL n)   = "APP" ++ show n
        show (SOUI_PSOL n)  = "UI"  ++ show n
        show (SOEG_PSOL n)  = "EG"  ++ show n
        show (SOUD_PSOL n)  = "UD"  ++ show n
        show (SOED1_PSOL n) = "ED"  ++ show n
        show (SOED2_PSOL n) = "ED"  ++ show n
        show (FO_PSOL x) = show x

instance Inference PSOLogic PolyadicallySOLLex where
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

        restriction (SOUD_PSOL n)  = Just (psopredicateEigenConstraint 
                                          (liftToSequent $ psolAppScheme (n - 1)) 
                                          -- XXX would be better to use
                                          -- contexts alone in line above
                                          (ss' $ universalScheme n)  
                                          (GammaV 1))

        restriction (SOED1_PSOL n)  = Just (psopredicateEigenConstraint 
                                           (liftToSequent $ psolAppScheme (n - 1)) 
                                           (ss' $ existentialScheme n)  
                                           (GammaV 1 :+: GammaV 2))

        restriction (FO_PSOL UD)  = Just (eigenConstraint stau 
                                        (ss' $ SOBind (All "v") phi) 
                                        (GammaV 1))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent taup

        restriction (FO_PSOL ED1) = Just (eigenConstraint stau 
                                        ((ss' $ SOBind (Some "v") phi) :-: ss' phiSp) 
                                        (GammaV 1 :+: GammaV 2))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  
                  stau = liftToSequent taup
        restriction _ = Nothing
        --

-- XXX Skipping derived rules for now.
parsePSOLogic :: Parsec String u [PSOLogic]
parsePSOLogic = try soRule <|> liftFO
    where liftFO = do r <- parseFOLogic empty
                      return (map FO_PSOL r)
          soRule = do r <- choice (map (try . string) [ "UI", "UD", "EG", "ED", "ABS","APP"])
                      ds <- many1 digit
                      let n = read ds :: Int
                      case r of 
                            r | r == "UI"   -> return [SOUI_PSOL n]
                              | r == "UD"   -> return [SOUD_PSOL n]
                              | r == "EG"   -> return [SOEG_PSOL n]
                              | r == "ED"   -> return [SOED1_PSOL n, SOED2_PSOL n]
                              | r == "ABS"  -> return [ABS_PSOL n]
                              | r == "APP"  -> return [APP_PSOL n]

parsePSOLProof :: String -> [DeductionLine PSOLogic PolyadicallySOLLex (Form Bool)]
parsePSOLProof = toDeductionMontegue parsePSOLogic psolFormulaParser

psolSeqParser = seqFormulaParser :: Parsec String () (PSOLSequentCalc Sequent)

psolCalc = NaturalDeductionCalc 
    { ndRenderer = MontegueStyle
    , ndParseProof = const parsePSOLProof -- XXX ignore derived rules for now
    , ndProcessLine = hoProcessLineMontegue
    , ndProcessLineMemo = Just hoProcessLineMontegueMemo
    , ndParseSeq = psolSeqParser
    }
