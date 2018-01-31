module Carnap.Languages.PurePropositional.Logic 
    ( DerivedRule(..),  PropSequentCalc
    , parsePropLogic, parseFitchPropLogic, parseMagnusSL, parseMagnusSLPlus, parseHardegreeSL, parseThomasBolducAndZachTFL
    , LogicBookPropLogic, MagnusSL, MagnusSLPlus, PropLogic, HardegreeSL, ThomasBolducAndZachTFL
    , magnusSLCalc, magnusSLPlusCalc, logicBookCalc, propCalc , hardegreeSLCalc, thomasBolducAndZachTFLCalc
    ) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
