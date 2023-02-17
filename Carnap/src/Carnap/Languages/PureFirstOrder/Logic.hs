{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.PureFirstOrder.Logic
        ( FOLogic(..)
        , parseFOLogic, folCalc
        , parseMontagueQCCalc, montagueQCCalc
        , parseMagnusQL, magnusQLCalc
        , parseThomasBolducAndZachFOL, thomasBolducAndZachFOLCalc
        , parseThomasBolducAndZachFOLCore, thomasBolducAndZachFOL2019Calc, thomasBolducAndZachFOLPlus2019Calc
        , parseLogicBookPD, logicBookPDCalc, logicBookPDPlusCalc, logicBookPDEPlusCalc
        , parseHausmanPL, hausmanPLCalc
        , parseHowardSnyderPL, howardSnyderPLCalc
        , parseIchikawaJenkinsQL, ichikawaJenkinsQLCalc
        , parseHardegreePL, hardegreePLCalc
        , parseTomassiQL, tomassiQLCalc
        , gallowPLCalc, gallowPLPlusCalc
        , GamutNDPlus(..), GamutNDCore(..), parseGamutNDPlus
        , goldfarbNDCalc, goldfarbBrownNDCalc, goldfarbNDPlusCalc, goldfarbBrownNDPlusCalc
        , ofFOLSys, ofFOLTreeSys, ofFOLSeqSys
        )
    where

import Carnap.Core.Data.Types
import Carnap.Calculi.Util
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.Tableau.Data
import Carnap.Languages.PureFirstOrder.Logic.Arthur
import Carnap.Languages.PureFirstOrder.Logic.Belot
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Languages.PureFirstOrder.Logic.Bonevac
import Carnap.Languages.PureFirstOrder.Logic.Carnap
import Carnap.Languages.PureFirstOrder.Logic.Cortens
import Carnap.Languages.PureFirstOrder.Logic.Davis
import Carnap.Languages.PureFirstOrder.Logic.EbelsDuggan
import Carnap.Languages.PureFirstOrder.Logic.Equivalence
import Carnap.Languages.PureFirstOrder.Logic.Gallow
import Carnap.Languages.PureFirstOrder.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Logic.Gentzen
import Carnap.Languages.PureFirstOrder.Logic.Goldfarb
import Carnap.Languages.PureFirstOrder.Logic.Hardegree
import Carnap.Languages.PureFirstOrder.Logic.Hausman
import Carnap.Languages.PureFirstOrder.Logic.HowardSnyder
import Carnap.Languages.PureFirstOrder.Logic.Hurley
import Carnap.Languages.PureFirstOrder.Logic.IchikawaJenkins
import Carnap.Languages.PureFirstOrder.Logic.Lemmon
import Carnap.Languages.PureFirstOrder.Logic.Lande
import Carnap.Languages.PureFirstOrder.Logic.KalishAndMontague
import Carnap.Languages.PureFirstOrder.Logic.Magnus
import Carnap.Languages.PureFirstOrder.Logic.OpenLogic
import Carnap.Languages.PureFirstOrder.Logic.Gregory
import Carnap.Languages.PureFirstOrder.Logic.ThomasBolducAndZach
import Carnap.Languages.PureFirstOrder.Logic.Tomassi
import Carnap.Languages.PureFirstOrder.Logic.Winkler 
import Carnap.Languages.PureFirstOrder.Logic.Rules

ofFOLSys :: (forall r . (Show r, Inference r PureLexiconFOL (Form Bool)) => 
             NaturalDeductionCalc r PureLexiconFOL (Form Bool) -> a) -> String -> Maybe a
ofFOLSys f sys | sys == "LogicBookPD"                     = Just $ f logicBookPDCalc
               | sys == "LogicBookPDE"                    = Just $ f logicBookPDECalc
               | sys == "LogicBookPDEPlus"                = Just $ f logicBookPDEPlusCalc
               | sys == "LogicBookPDPlus"                 = Just $ f logicBookPDPlusCalc
               | sys == "arthurQL"                        = Just $ f arthurQLCalc
               | sys == "belotPD"                         = Just $ f belotPDCalc       
               | sys == "belotPDE"                        = Just $ f belotPDECalc      
               | sys == "belotPDEPlus"                    = Just $ f belotPDEPlusCalc  
               | sys == "belotPDPlus"                     = Just $ f belotPDPlusCalc   
               | sys == "bonevacQL"                       = Just $ f bonevacQLCalc
               | sys == "cortensQL"                       = Just $ f cortensQLCalc
               | sys == "davisQL"                         = Just $ f davisQLCalc
               | sys == "ebelsDugganFOL"                  = Just $ f ebelsDugganFOLCalc
               | sys == "firstOrder"                      = Just $ f folCalc
               | sys == "firstOrderNonC"                  = Just $ f folCalcNonC
               | sys == "gallowPL"                        = Just $ f gallowPLCalc
               | sys == "gallowPLPlus"                    = Just $ f gallowPLPlusCalc
               | sys == "gamutND"                         = Just $ f gamutNDCalc
               | sys == "gamutNDPlus"                     = Just $ f gamutNDPlusCalc
               | sys == "goldfarbAltND"                   = Just $ f goldfarbBrownNDCalc
               | sys == "goldfarbAltNDPlus"               = Just $ f goldfarbBrownNDPlusCalc
               | sys == "goldfarbND"                      = Just $ f goldfarbNDCalc
               | sys == "goldfarbNDPlus"                  = Just $ f goldfarbNDPlusCalc
               | sys == "gregoryPD"                       = Just $ f gregoryPDCalc
               | sys == "gregoryPDE"                      = Just $ f gregoryPDECalc
               | sys == "hardegreePL"                     = Just $ f hardegreePLCalc
               | sys == "hardegreePL2006"                 = Just $ f hardegreePL2006Calc
               | sys == "hausmanPL"                       = Just $ f hausmanPLCalc
               | sys == "howardSnyderPL"                  = Just $ f howardSnyderPLCalc
               | sys == "hurleyPL"                        = Just $ f hurleyPLCalc
               | sys == "ichikawaJenkinsQL"               = Just $ f ichikawaJenkinsQLCalc
               | sys == "lemmonQuant"                     = Just $ f lemmonQuantCalc
               | sys == "landeQuant"                      = Just $ f landeQuantCalc
               | sys == "magnusQL"                        = Just $ f magnusQLCalc
               | sys == "magnusQLPlus"                    = Just $ f magnusQLPlusCalc
               | sys == "montagueQC"                      = Just $ f montagueQCCalc
               | sys == "thomasBolducAndZachFOL"          = Just $ f thomasBolducAndZachFOLCalc
               | sys == "thomasBolducAndZachFOL2019"      = Just $ f thomasBolducAndZachFOL2019Calc
               | sys == "thomasBolducAndZachFOLCore"      = Just $ f thomasBolducAndZachFOLCoreCalc
               | sys == "thomasBolducAndZachFOLPlus2019"  = Just $ f thomasBolducAndZachFOLPlus2019Calc
               | sys == "tomassiQL"                       = Just $ f tomassiQLCalc
               | sys == "winklerFOL"                      = Just $ f winklerFOLCalc
               | sys == "zachFOLEq"                       = Just $ f zachFOLEqCalc
               | otherwise                                = Nothing

ofFOLTreeSys :: (forall r . 
                    ( Show r
                    , Inference r PureLexiconFOL (Form Bool)
                    , StructuralInference r PureLexiconFOL (ProofTree r PureLexiconFOL (Form Bool))
                    , StructuralOverride r (ProofTree r PureLexiconFOL (Form Bool))
                 ) => 
              TableauCalc PureLexiconFOL (Form Bool) r -> a) -> String -> Maybe a
ofFOLTreeSys f sys | sys == "openLogicFOLNK"             = Just $ f openLogicFONKCalc
                   | otherwise                           = Nothing

ofFOLSeqSys :: (forall r . 
                    ( Show r
                    , CoreInference r PureLexiconFOL (Form Bool)
                    , SpecifiedUnificationType r
                 ) => 
              TableauCalc PureLexiconFOL (Form Bool) r -> a) -> String -> Maybe a
ofFOLSeqSys f sys | sys == "foLK"                     = Just $ f gentzenFOLKCalc 
                  | sys == "foLJ"                     = Just $ f gentzenFOLJCalc 
                  | sys == "openLogicFOLK"            = Just $ f olpFOLKCalc 
                  | sys == "openLogicFOLJ"            = Just $ f olpFOLJCalc 
                  | otherwise                         = Nothing
