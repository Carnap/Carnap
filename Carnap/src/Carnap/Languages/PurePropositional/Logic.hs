module Carnap.Languages.PurePropositional.Logic 
    ( DerivedRule(..),  PropSequentCalc
    , parsePropLogic, parseLogicBookSD, parseMagnusSL, parseMagnusSLPlus, parseHardegreeSL, parseThomasBolducAndZachTFL
    , LogicBookSD, MagnusSL, MagnusSLPlus, PropLogic, HardegreeSL, ThomasBolducAndZachTFL
    , magnusSLCalc, magnusSLPlusCalc, logicBookSD, propCalc , hardegreeSLCalc, thomasBolducAndZachTFLCalc
    ) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
