module Carnap.Languages.HigherOrderArithmetic.Logic.OpenLogic (openLogicArithExHOArithNKCalc)
where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Logic.OpenLogic
import Carnap.Languages.HigherOrderArithmetic.Parser 
import Carnap.Languages.HigherOrderArithmetic.Syntax
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Tableau.Data

openLogicArithExHOArithNKCalc :: TableauCalc UntypedHigherOrderArithLex (Form Bool) (OpenLogicFONK UntypedHigherOrderArithLex) 
openLogicArithExHOArithNKCalc = mkTBCalc
    { tbParseForm = untypedHigherOrderArithmeticParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }
