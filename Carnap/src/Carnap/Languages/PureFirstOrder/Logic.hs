module Carnap.Languages.PureFirstOrder.Logic
        ( FOLogic(..), parseFOLogic, parseMagnusQL, parseThomasBolducAndZachFOL, DerivedRule(..)
        , folCalc, magnusQLCalc, thomasBolducAndZachFOLCalc)
    where

import Carnap.Languages.PureFirstOrder.Logic.Magnus
import Carnap.Languages.PureFirstOrder.Logic.KalishAndMontegue
import Carnap.Languages.PureFirstOrder.Logic.ThomasBolducAndZach
import Carnap.Languages.PureFirstOrder.Logic.Rules
