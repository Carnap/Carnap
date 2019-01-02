module Carnap.Languages.PurePropositional.Logic 
    ( DerivedRule(..),  PropSequentCalc
    , parsePropLogic, parseMontagueSC, parseLogicBookSD,
    parseLogicBookSDPlus, parseMagnusSL, parseMagnusSLPlus,
    parseHardegreeSL, parseThomasBolducAndZachTFL, parseTomassiPL,
    parseHausmanSL, parseHowardSnyderSL, PropLogic, LogicBookSD, LogicBookSDPlus, MagnusSL,
    MagnusSLPlus, MontagueSC, HardegreeSL, ThomasBolducAndZachTFL,
    TomassiPL, HausmanSL, HowardSnyderSL , propCalc, magnusSLCalc,
    magnusSLPlusCalc, logicBookSDCalc, logicBookSDPlusCalc, montagueSCCalc,
    hardegreeSLCalc, thomasBolducAndZachTFLCalc, tomassiPLCalc,
    hausmanSLCalc, howardSnyderSLCalc
    ) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Carnap
import Carnap.Languages.PurePropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.Hausman
import Carnap.Languages.PurePropositional.Logic.HowardSnyder
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
import Carnap.Languages.PurePropositional.Logic.Tomassi
