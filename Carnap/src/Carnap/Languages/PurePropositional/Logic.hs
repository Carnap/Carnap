module Carnap.Languages.PurePropositional.Logic 
    ( DerivedRule(..),  PropSequentCalc
    , parsePropLogic, parseMontagueSC, parseLogicBookSD, parseLogicBookSDPlus, parseMagnusSL, parseMagnusSLPlus, parseHardegreeSL, parseThomasBolducAndZachTFL, parseTomassiPL
    , PropLogic, LogicBookSD, LogicBookSDPlus, MagnusSL, MagnusSLPlus, MontagueSC, HardegreeSL, ThomasBolducAndZachTFL, TomassiPL
    , propCalc, magnusSLCalc, magnusSLPlusCalc, logicBookSDCalc, logicBookSDPlusCalc, montagueSCCalc, hardegreeSLCalc, thomasBolducAndZachTFLCalc, tomassiPLCalc, 
    ) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.Carnap
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
import Carnap.Languages.PurePropositional.Logic.Tomassi
