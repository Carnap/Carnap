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
        , goldfarbNDCalc, goldfarbAltNDCalc, goldfarbNDPlusCalc, goldfarbAltNDPlusCalc
        , ofFOLSys, ofFOLTreeSys, ofFOLSeqSys
        )
    where

import Carnap.Core.Data.Types
import Carnap.Calculi.Util
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.Tableau.Data
import Carnap.Languages.PureFirstOrder.Logic.Carnap
import Carnap.Languages.PureFirstOrder.Logic.Magnus
import Carnap.Languages.PureFirstOrder.Logic.KalishAndMontague
import Carnap.Languages.PureFirstOrder.Logic.Gallow
import Carnap.Languages.PureFirstOrder.Logic.ThomasBolducAndZach
import Carnap.Languages.PureFirstOrder.Logic.EbelsDuggan
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Languages.PureFirstOrder.Logic.Hausman
import Carnap.Languages.PureFirstOrder.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Logic.HowardSnyder
import Carnap.Languages.PureFirstOrder.Logic.Hurley
import Carnap.Languages.PureFirstOrder.Logic.Hardegree
import Carnap.Languages.PureFirstOrder.Logic.Bonevac
import Carnap.Languages.PureFirstOrder.Logic.Goldfarb
import Carnap.Languages.PureFirstOrder.Logic.Tomassi
import Carnap.Languages.PureFirstOrder.Logic.IchikawaJenkins
import Carnap.Languages.PureFirstOrder.Logic.Gentzen
import Carnap.Languages.PureFirstOrder.Logic.OpenLogic
import Carnap.Languages.PureFirstOrder.Logic.Equivalence
import Carnap.Languages.PureFirstOrder.Logic.Rules

ofFOLSys :: (forall r . (Show r, Inference r PureLexiconFOL (Form Bool)) => 
             NaturalDeductionCalc r PureLexiconFOL (Form Bool) -> a) -> String -> Maybe a
ofFOLSys f sys | sys == "firstOrder"                      = Just $ f folCalc
               | sys == "montagueQC"                      = Just $ f montagueQCCalc
               | sys == "magnusQL"                        = Just $ f magnusQLCalc
               | sys == "magnusQLPlus"                    = Just $ f magnusQLPlusCalc
               | sys == "thomasBolducAndZachFOL"          = Just $ f thomasBolducAndZachFOLCalc
               | sys == "thomasBolducAndZachFOLCore"      = Just $ f thomasBolducAndZachFOLCoreCalc
               | sys == "thomasBolducAndZachFOL2019"      = Just $ f thomasBolducAndZachFOL2019Calc
               | sys == "thomasBolducAndZachFOLPlus2019"  = Just $ f thomasBolducAndZachFOLPlus2019Calc
               | sys == "ebelsDugganFOL"                  = Just $ f ebelsDugganFOLCalc
               | sys == "LogicBookPD"                     = Just $ f logicBookPDCalc
               | sys == "LogicBookPDPlus"                 = Just $ f logicBookPDPlusCalc
               | sys == "LogicBookPDE"                    = Just $ f logicBookPDECalc
               | sys == "LogicBookPDEPlus"                = Just $ f logicBookPDEPlusCalc
               | sys == "hausmanPL"                       = Just $ f hausmanPLCalc
               | sys == "gamutND"                         = Just $ f gamutNDCalc
               | sys == "gamutNDPlus"                     = Just $ f gamutNDPlusCalc
               | sys == "gallowPL"                        = Just $ f gallowPLCalc
               | sys == "gallowPLPlus"                    = Just $ f gallowPLPlusCalc
               | sys == "howardSnyderPL"                  = Just $ f howardSnyderPLCalc
               | sys == "hurleyPL"                        = Just $ f hurleyPLCalc
               | sys == "ichikawaJenkinsQL"               = Just $ f ichikawaJenkinsQLCalc
               | sys == "hardegreePL"                     = Just $ f hardegreePLCalc
               | sys == "bonevacQL"                       = Just $ f bonevacQLCalc
               | sys == "goldfarbND"                      = Just $ f goldfarbNDCalc
               | sys == "goldfarbAltND"                   = Just $ f goldfarbAltNDCalc
               | sys == "goldfarbNDPlus"                  = Just $ f goldfarbNDPlusCalc
               | sys == "goldfarbAltNDPlus"               = Just $ f goldfarbAltNDPlusCalc
               | sys == "tomassiQL"                       = Just $ f tomassiQLCalc
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
