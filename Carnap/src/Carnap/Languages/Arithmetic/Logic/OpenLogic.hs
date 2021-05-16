module Carnap.Languages.Arithmetic.Logic.OpenLogic (openLogicArithNKCalc, openLogicExtendedArithNKCalc)
where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Logic.OpenLogic
import Carnap.Languages.Arithmetic.Parser 
import Carnap.Languages.Arithmetic.Syntax
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Tableau.Data

openLogicArithNKCalc :: TableauCalc ArithLex (Form Bool) (OpenLogicAxFONK ArithLex) 
openLogicArithNKCalc = mkTBCalc
    { tbParseForm = arithmeticParser
    , tbParseRule = parseOpenLogicAxFONK
    , tbNotation = dropOuterParens
    }

openLogicExtendedArithNKCalc :: TableauCalc ExtendedArithLex (Form Bool) (OpenLogicAxFONK ExtendedArithLex) 
openLogicExtendedArithNKCalc = mkTBCalc
    { tbParseForm = arithmeticExtendedParser
    , tbParseRule = parseOpenLogicAxFONK
    , tbNotation = dropOuterParens
    , tbParseAxiomScheme = Just arithmeticExtendedSchemaParser
    }
