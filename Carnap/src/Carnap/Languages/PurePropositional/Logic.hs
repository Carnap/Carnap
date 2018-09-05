module Carnap.Languages.PurePropositional.Logic 
    ( DerivedRule(..),  PropSequentCalc
    , parseMontagueSC, parseLogicBookSD, parseLogicBookSDPlus, parseMagnusSL, parseMagnusSLPlus, parseHardegreeSL, parseThomasBolducAndZachTFL, parseTomassiPL
    , LogicBookSD, LogicBookSDPlus, MagnusSL, MagnusSLPlus, MontagueSC, HardegreeSL, ThomasBolducAndZachTFL, TomassiPL
    , magnusSLCalc, magnusSLPlusCalc, logicBookSDCalc, logicBookSDPlusCalc, montagueSCCalc, hardegreeSLCalc, thomasBolducAndZachTFLCalc, tomassiPLCalc, 
    ) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
import Carnap.Languages.PurePropositional.Logic.Tomassi
