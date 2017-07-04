module Carnap.Languages.PurePropositional.Logic 
    ( parsePropLogic, parseFitchPropLogic, parseMagnusSL, parsePropProof, parseFitchPropProof, LogicBookPropLogic,
    DerivedRule(..),  PropSequentCalc, MagnusSL, PropLogic, magnusSLCalc, logicBookCalc, propCalc) where

import Carnap.Languages.PurePropositional.Logic.Rules (PropSequentCalc,DerivedRule(..))
import Carnap.Languages.PurePropositional.Logic.KalishAndMontegue
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Logic.Magnus

