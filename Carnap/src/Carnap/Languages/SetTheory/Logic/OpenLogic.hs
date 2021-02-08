module Carnap.Languages.SetTheory.Logic.OpenLogic (openLogicESTNKCalc, openLogicSTNKCalc)
where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Logic.OpenLogic
import Carnap.Languages.SetTheory.Parser 
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Tableau.Data

openLogicSTNKCalc :: TableauCalc StrictSetTheoryLex (Form Bool) (OpenLogicFONK StrictSetTheoryLex) 
openLogicSTNKCalc = mkTBCalc
    { tbParseForm = strictSetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

openLogicESTNKCalc :: TableauCalc ElementarySetTheoryLex (Form Bool) (OpenLogicFONK ElementarySetTheoryLex) 
openLogicESTNKCalc = mkTBCalc
    { tbParseForm = elementarySetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }
