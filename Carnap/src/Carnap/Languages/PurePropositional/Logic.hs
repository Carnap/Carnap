module Carnap.Languages.PurePropositional.Logic 
    ( DerivedRule(..),  PropSequentCalc
    , parsePropLogic, parseFitchPropLogic, parseMagnusSL, parseMagnusSLPlus
    , LogicBookPropLogic, MagnusSL, MagnusSLPlus, PropLogic
    , magnusSLCalc, magnusSLPlusCalc, logicBookCalc, propCalc) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.KalishAndMontegue
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Magnus

