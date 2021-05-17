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

openLogicExSTNKCalc :: TableauCalc ExtendedStrictSetTheoryLex (Form Bool) (OpenLogicAxFONK ExtendedStrictSetTheoryLex) 
openLogicExSTNKCalc = mkTBCalc
    { tbParseForm = extendedStrictSetTheoryParser
    , tbParseRule = parseOpenLogicAxFONK
    , tbNotation = dropOuterParens
    , tbParseAxiomScheme = Just extendedStrictSetTheorySchemaParser
    }

openLogicESTNKCalc :: TableauCalc ElementarySetTheoryLex (Form Bool) (OpenLogicFONK ElementarySetTheoryLex) 
openLogicESTNKCalc = mkTBCalc
    { tbParseForm = elementarySetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

openLogicExESTNKCalc :: TableauCalc ExtendedElementarySetTheoryLex (Form Bool) (OpenLogicAxFONK ExtendedElementarySetTheoryLex) 
openLogicExESTNKCalc = mkTBCalc
    { tbParseForm = extendedElementarySetTheoryParser
    , tbParseRule = parseOpenLogicAxFONK
    , tbNotation = dropOuterParens
    , tbParseAxiomScheme = Just extendedElementarySetTheorySchemaParser
    }

openLogicSSTNKCalc :: TableauCalc SeparativeSetTheoryLex (Form Bool) (OpenLogicFONK SeparativeSetTheoryLex) 
openLogicSSTNKCalc = mkTBCalc
    { tbParseForm = separativeSetTheoryParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

openLogicExSSTNKCalc :: TableauCalc ExtendedSeparativeSetTheoryLex (Form Bool) (OpenLogicAxFONK ExtendedSeparativeSetTheoryLex) 
openLogicExSSTNKCalc = mkTBCalc
    { tbParseForm = extendedSeparativeSetTheoryParser
    , tbParseRule = parseOpenLogicAxFONK
    , tbNotation = dropOuterParens
    , tbParseAxiomScheme = Just extendedSeparativeSetTheorySchemaParser
    }
