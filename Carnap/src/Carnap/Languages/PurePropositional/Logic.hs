{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.PurePropositional.Logic 
    ( PropSequentCalc
    , parsePropLogic, PropLogic, propCalc, propCalcStrict
    , parseMontagueSC, MontagueSC, montagueSCCalc
    , parseLogicBookSD, LogicBookSD, logicBookSDCalc
    , parseLogicBookSDPlus,  LogicBookSDPlus, logicBookSDPlusCalc
    , parseHowardSnyderSL, HowardSnyderSL, howardSnyderSLCalc
    , parseIchikawaJenkinsSL, IchikawaJenkinsSL, ichikawaJenkinsSLCalc
    , parseHausmanSL, HausmanSL, hausmanSLCalc
    , parseMagnusSL, MagnusSL, magnusSLCalc
    , parseMagnusSLPlus, MagnusSLPlus, magnusSLPlusCalc
    , parseThomasBolducAndZachTFL, ThomasBolducAndZachTFL, thomasBolducAndZachTFLCalc
    , parseThomasBolducAndZachTFLCore, ThomasBolducAndZachTFLCore, thomasBolducAndZachTFL2019Calc
    , parseEbelsDugganTFL, EbelsDugganTFL, ebelsDugganTFLCalc
    , parseTomassiPL, TomassiPL, tomassiPLCalc
    , parseHardegreeSL2006 , parseHardegreeSL, HardegreeSL, HardegreeSL2006, hardegreeSLCalc
    , parseBonevacSL, BonevacSL, bonevacSLCalc
    , parseHurleySL, HurleySL, hurleySLCalc
    , parseGentzenPropNJ, GentzenPropNJ, gentzenPropNJCalc
    , parseGentzenPropNK, GentzenPropNK, gentzenPropNKCalc
    , ofPropSys, ofPropTreeSys, ofPropSeqSys
    ) where

import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.Tableau.Data
import Carnap.Core.Data.Types
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc)
import Carnap.Languages.PurePropositional.Logic.Allen
import Carnap.Languages.PurePropositional.Logic.Belot
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Bonevac
import Carnap.Languages.PurePropositional.Logic.Carnap
import Carnap.Languages.PurePropositional.Logic.EbelsDuggan
import Carnap.Languages.PurePropositional.Logic.Equivalence
import Carnap.Languages.PurePropositional.Logic.Gallow
import Carnap.Languages.PurePropositional.Logic.Gamut
import Carnap.Languages.PurePropositional.Logic.Gentzen
import Carnap.Languages.PurePropositional.Logic.Goldfarb
import Carnap.Languages.PurePropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.Hausman
import Carnap.Languages.PurePropositional.Logic.HowardSnyder
import Carnap.Languages.PurePropositional.Logic.Hurley
import Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.OpenLogic
import Carnap.Languages.PurePropositional.Logic.Gregory
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
import Carnap.Languages.PurePropositional.Logic.Tomassi
import Carnap.Languages.PurePropositional.Logic.Winkler

ofPropSys :: (forall r . (Show r, Inference r PurePropLexicon (Form Bool)) =>
              NaturalDeductionCalc r PurePropLexicon (Form Bool) -> a) -> String -> Maybe a
ofPropSys f sys | sys == "LogicBookSD"                   = Just $ f logicBookSDCalc
                | sys == "LogicBookSDPlus"               = Just $ f logicBookSDPlusCalc
                | sys == "allenSL"                       = Just $ f allenSLCalc
                | sys == "allenSLPlus"                   = Just $ f allenSLPlusCalc
                | sys == "bonevacSL"                     = Just $ f bonevacSLCalc
                | sys == "belotSD"                       = Just $ f belotSDCalc
                | sys == "belotSDPlus"                   = Just $ f belotSDPlusCalc
                | sys == "ebelsDugganTFL"                = Just $ f ebelsDugganTFLCalc 
                | sys == "gallowSL"                      = Just $ f gallowSLCalc
                | sys == "gallowSLPlus"                  = Just $ f gallowSLPlusCalc
                | sys == "gamutIPND"                     = Just $ f gamutIPNDCalc
                | sys == "gamutMPND"                     = Just $ f gamutMPNDCalc
                | sys == "gamutPND"                      = Just $ f gamutPNDCalc
                | sys == "gamutPNDPlus"                  = Just $ f gamutPNDPlusCalc
                | sys == "goldfarbPropND"                = Just $ f goldfarbPropNDCalc
                | sys == "hardegreeSL"                   = Just $ f hardegreeSLCalc
                | sys == "hardegreeSL2006"               = Just $ f hardegreeSL2006Calc
                | sys == "hausmanSL"                     = Just $ f hausmanSLCalc
                | sys == "hausmanSL"                     = Just $ f hausmanSLCalc
                | sys == "howardSnyderSL"                = Just $ f howardSnyderSLCalc
                | sys == "hurleySL"                      = Just $ f hurleySLCalc
                | sys == "ichikawaJenkinsSL"             = Just $ f ichikawaJenkinsSLCalc
                | sys == "johnsonSL"                     = Just $ f allenSLCalc
                | sys == "johnsonSLPlus"                 = Just $ f allenSLPlusCalc
                | sys == "magnusSL"                      = Just $ f magnusSLCalc
                | sys == "magnusSLPlus"                  = Just $ f magnusSLPlusCalc
                | sys == "montagueSC"                    = Just $ f montagueSCCalc
                | sys == "gregorySD"                     = Just $ f gregorySDCalc
                | sys == "gregorySDE"                    = Just $ f gregorySDECalc
                | sys == "prop"                          = Just $ f propCalc
                | sys == "propStrict"                    = Just $ f propCalcStrict
                | sys == "thomasBolducAndZachTFL"        = Just $ f thomasBolducAndZachTFLCalc
                | sys == "thomasBolducAndZachTFL2019"    = Just $ f thomasBolducAndZachTFL2019Calc
                | sys == "thomasBolducAndZachTFLCore"    = Just $ f thomasBolducAndZachTFLCoreCalc
                | sys == "tomassiPL"                     = Just $ f tomassiPLCalc
                | sys == "winklerTFL"                    = Just $ f winklerTFLCalc 
                | sys == "zachPropEq"                    = Just $ f zachPropEqCalc
                | otherwise                              = Nothing

ofPropTreeSys :: (forall r . 
                    ( Show r
                    , Inference r PurePropLexicon (Form Bool)
                    , StructuralInference r PurePropLexicon (ProofTree r PurePropLexicon (Form Bool))
                    , StructuralOverride r (ProofTree r PurePropLexicon (Form Bool))
                 ) => 
              TableauCalc PurePropLexicon (Form Bool) r -> a) -> String -> Maybe a
ofPropTreeSys f sys | sys == "propNJ"                     = Just $ f gentzenPropNJCalc 
                    | sys == "propNK"                     = Just $ f gentzenPropNKCalc 
                    | sys == "openLogicNK"                = Just $ f olpPropNKCalc 
                    | otherwise                           = Nothing

ofPropSeqSys :: (forall r . 
                    ( Show r
                    , CoreInference r PurePropLexicon (Form Bool)
                    , SpecifiedUnificationType r
                 ) => 
              TableauCalc PurePropLexicon (Form Bool) r -> a) -> String -> Maybe a
ofPropSeqSys f sys | sys == "propLJ"                     = Just $ f gentzenPropLJCalc 
                   | sys == "propLK"                     = Just $ f gentzenPropLKCalc 
                   | sys == "openLogicPropLK"            = Just $ f olpPropLKCalc 
                   | sys == "openLogicPropLJ"            = Just $ f olpPropLJCalc 
                   | otherwise                           = Nothing
