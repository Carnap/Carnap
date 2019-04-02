module Carnap.Languages.PureFirstOrder.Logic
        ( FOLogic(..)
        , parseFOLogic, folCalc
        , parseMontagueQCCalc, montagueQCCalc
        , parseMagnusQL, magnusQLCalc
        , parseThomasBolducAndZachFOL, thomasBolducAndZachFOLCalc
        , parseHardegreePL, hardegreePLCalc
        , parseLogicBookPD, logicBookPDCalc, logicBookPDPlusCalc
        , parseHausmanPL, hausmanPLCalc
        , parseHowardSnyderPL, howardSnyderPLCalc
        , parseIchikawaJenkinsQL, ichikawaJenkinsQLCalc
        , goldfarbNDCalc, goldfarbAltNDCalc, goldfarbNDPlusCalc, goldfarbAltNDPlusCalc
        )
    where

import Carnap.Languages.PureFirstOrder.Logic.Carnap
import Carnap.Languages.PureFirstOrder.Logic.Magnus
import Carnap.Languages.PureFirstOrder.Logic.KalishAndMontague
import Carnap.Languages.PureFirstOrder.Logic.ThomasBolducAndZach
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Languages.PureFirstOrder.Logic.Hausman
import Carnap.Languages.PureFirstOrder.Logic.HowardSnyder
import Carnap.Languages.PureFirstOrder.Logic.Hardegree
import Carnap.Languages.PureFirstOrder.Logic.Goldfarb
import Carnap.Languages.PureFirstOrder.Logic.IchikawaJenkins
import Carnap.Languages.PureFirstOrder.Logic.Rules
