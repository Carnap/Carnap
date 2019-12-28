{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.PureFirstOrder.Logic
        ( FOLogic(..)
        , parseFOLogic, folCalc
        , parseMontagueQCCalc, montagueQCCalc
        , parseMagnusQL, magnusQLCalc
        , parseThomasBolducAndZachFOL, thomasBolducAndZachFOLCalc
        , parseThomasBolducAndZachFOLCore, thomasBolducAndZachFOL2019Calc, thomasBolducAndZachFOLPlus2019Calc
        , parseLogicBookPD, logicBookPDCalc, logicBookPDPlusCalc
        , parseHausmanPL, hausmanPLCalc
        , parseHowardSnyderPL, howardSnyderPLCalc
        , parseIchikawaJenkinsQL, ichikawaJenkinsQLCalc
        , parseHardegreePL, hardegreePLCalc
        , goldfarbNDCalc, goldfarbAltNDCalc, goldfarbNDPlusCalc, goldfarbAltNDPlusCalc
        , ofFOLSys
        )
    where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.PureFirstOrder.Logic.Carnap
import Carnap.Languages.PureFirstOrder.Logic.Magnus
import Carnap.Languages.PureFirstOrder.Logic.KalishAndMontague
import Carnap.Languages.PureFirstOrder.Logic.ThomasBolducAndZach
import Carnap.Languages.PureFirstOrder.Logic.EbelsDuggan
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Languages.PureFirstOrder.Logic.Hausman
import Carnap.Languages.PureFirstOrder.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Logic.HowardSnyder
import Carnap.Languages.PureFirstOrder.Logic.Hardegree
import Carnap.Languages.PureFirstOrder.Logic.Goldfarb
import Carnap.Languages.PureFirstOrder.Logic.IchikawaJenkins
import Carnap.Languages.PureFirstOrder.Logic.Rules

ofFOLSys :: (forall r . (Show r, Inference r PureLexiconFOL (Form Bool)) => 
             NaturalDeductionCalc r PureLexiconFOL (Form Bool) -> a) -> String -> Maybe a
ofFOLSys f sys | sys == "firstOrder"                      = Just $ f folCalc
               | sys == "montagueQC"                      = Just $ f montagueQCCalc 
               | sys == "magnusQL"                        = Just $ f magnusQLCalc 
               | sys == "thomasBolducAndZachFOL"          = Just $ f thomasBolducAndZachFOLCalc 
               | sys == "thomasBolducAndZachFOL2019"      = Just $ f thomasBolducAndZachFOL2019Calc 
               | sys == "thomasBolducAndZachFOLPlus2019"  = Just $ f thomasBolducAndZachFOLPlus2019Calc 
               | sys == "ebelsDugganFOL"                  = Just $ f ebelsDugganFOLCalc
               | sys == "LogicBookPD"                     = Just $ f logicBookPDCalc 
               | sys == "LogicBookPDPlus"                 = Just $ f logicBookPDPlusCalc 
               | sys == "hausmanPL"                       = Just $ f hausmanPLCalc 
               | sys == "gamutND"                         = Just $ f gamutNDCalc
               | sys == "howardSnyderPL"                  = Just $ f howardSnyderPLCalc 
               | sys == "ichikawaJenkinsQL"               = Just $ f ichikawaJenkinsQLCalc
               | sys == "hardegreePL"                     = Just $ f hardegreePLCalc 
               | sys == "goldfarbAltND"                   = Just $ f goldfarbAltNDCalc
               | sys == "goldfarbNDPlus"                  = Just $ f goldfarbNDPlusCalc
               | sys == "goldfarbAltNDPlus"               = Just $ f goldfarbAltNDPlusCalc
               | otherwise                                = Nothing
