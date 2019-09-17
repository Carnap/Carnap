{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.PurePropositional.Logic 
    ( PropSequentCalc
    , parsePropLogic, PropLogic, propCalc
    , parseMontagueSC, MontagueSC, montagueSCCalc
    , parseLogicBookSD, LogicBookSD, logicBookSDCalc
    , parseLogicBookSDPlus,  LogicBookSDPlus, logicBookSDPlusCalc
    , parseHowardSnyderSL, HowardSnyderSL, howardSnyderSLCalc
    , parseIchikawaJenkinsSL, IchikawaJenkinsSL, ichikawaJenkinsSLCalc
    , parseHausmanSL, HausmanSL, hausmanSLCalc
    , parseMagnusSL, MagnusSL, magnusSLCalc
    , parseMagnusSLPlus, MagnusSLPlus, magnusSLPlusCalc
    , parseThomasBolducAndZachTFL, ThomasBolducAndZachTFL, thomasBolducAndZachTFLCalc
    , parseEbelsDugganTFL, EbelsDugganTFL, ebelsDugganTFLCalc
    , parseTomassiPL, TomassiPL, tomassiPLCalc
    , parseHardegreeSL, HardegreeSL, hardegreeSLCalc
    , parseRipleyLNJ, RipleyLNJ, ripleyLNJCalc
    , ofPropSys
    ) where

import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Core.Data.Types
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc)
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Carnap
import Carnap.Languages.PurePropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.Hausman
import Carnap.Languages.PurePropositional.Logic.HowardSnyder
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
import Carnap.Languages.PurePropositional.Logic.EbelsDuggan
import Carnap.Languages.PurePropositional.Logic.Tomassi
import Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
import Carnap.Languages.PurePropositional.Logic.Ripley

ofPropSys :: (forall r . (Show r, Inference r PurePropLexicon (Form Bool)) => 
              NaturalDeductionCalc r PurePropLexicon (Form Bool) -> a) -> String -> Maybe a
ofPropSys f sys | sys == "prop"                      = Just $ f propCalc 
                | sys == "montagueSC"                = Just $ f montagueSCCalc 
                | sys == "LogicBookSD"               = Just $ f logicBookSDCalc 
                | sys == "LogicBookSDPlus"           = Just $ f logicBookSDPlusCalc 
                | sys == "hausmanSL"                 = Just $ f hausmanSLCalc 
                | sys == "howardSnyderSL"            = Just $ f howardSnyderSLCalc 
                | sys == "ichikawaJenkinsSL"         = Just $ f ichikawaJenkinsSLCalc
                | sys == "hausmanSL"                 = Just $ f hausmanSLCalc
                | sys == "magnusSL"                  = Just $ f magnusSLCalc 
                | sys == "magnusSLPlus"              = Just $ f magnusSLPlusCalc 
                | sys == "thomasBolducAndZachTFL"    = Just $ f thomasBolducAndZachTFLCalc 
                | sys == "ebelsDugganTFL"            = Just $ f ebelsDugganTFLCalc 
                | sys == "tomassiPL"                 = Just $ f tomassiPLCalc
                | sys == "hardegreeSL"               = Just $ f hardegreeSLCalc 
                | sys == "ripleyLNJ"                 = Just $ f ripleyLNJCalc
                | otherwise                          = Nothing
