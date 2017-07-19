module Carnap.Languages.PurePropositional.Logic 
    ( DerivedRule(..),  PropSequentCalc
    , parsePropLogic, parseFitchPropLogic, parseMagnusSL, parseMagnusSLPlus, parseHardegreeSL
    , LogicBookPropLogic, MagnusSL, MagnusSLPlus, PropLogic, HardegreeSL
    , magnusSLCalc, magnusSLPlusCalc, logicBookCalc, propCalc , hardegreeSLCalc ) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.KalishAndMontegue
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.Hardegree

