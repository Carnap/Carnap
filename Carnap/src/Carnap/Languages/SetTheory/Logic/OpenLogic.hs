module Carnap.Languages.SetTheory.Logic.OpenLogic 
( openLogicSTNKCalc, openLogicExSTNKCalc
, openLogicESTNKCalc, openLogicExESTNKCalc
, openLogicSSTNKCalc, openLogicExSSTNKCalc
) where

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

openLogicExSTNKCalc :: TableauCalc ExtendedStrictSetTheoryLex (Form Bool) (OpenLogicFONK ExtendedStrictSetTheoryLex) 
openLogicExSTNKCalc = mkTBCalc
    { tbParseForm = extendedStrictSetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

openLogicESTNKCalc :: TableauCalc ElementarySetTheoryLex (Form Bool) (OpenLogicFONK ElementarySetTheoryLex) 
openLogicESTNKCalc = mkTBCalc
    { tbParseForm = elementarySetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

openLogicExESTNKCalc :: TableauCalc ExtendedElementarySetTheoryLex (Form Bool) (OpenLogicFONK ExtendedElementarySetTheoryLex) 
openLogicExESTNKCalc = mkTBCalc
    { tbParseForm = extendedElementarySetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

openLogicSSTNKCalc :: TableauCalc SeparativeSetTheoryLex (Form Bool) (OpenLogicFONK SeparativeSetTheoryLex) 
openLogicSSTNKCalc = mkTBCalc
    { tbParseForm = separativeSetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

openLogicExSSTNKCalc :: TableauCalc ExtendedSeparativeSetTheoryLex (Form Bool) (OpenLogicFONK ExtendedSeparativeSetTheoryLex) 
openLogicExSSTNKCalc = mkTBCalc
    { tbParseForm = extendedSeparativeSetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }
