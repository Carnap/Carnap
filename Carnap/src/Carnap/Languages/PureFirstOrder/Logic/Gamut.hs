{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gamut (gamutNDCalc, parseGamutND) where

import Text.Parsec
import Data.Char
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,subst,FirstOrder)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Gamut
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser (parseSeqOver)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules

data GamutND = ND GamutPND
    deriving Eq

instance Show GamutND where
        show (ND x) = show x

instance Inference GamutND PureLexiconFOL (Form Bool) where

        premisesOf (ND x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf (ND x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference (ND x) = indirectInference x

        isAssumption (ND x) = isAssumption x
        isAssumption _ = False

parseGamutND rtc = map ND <$> parseGamutPND rtc

parseGamutNDProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GamutND PureLexiconFOL (Form Bool)]
parseGamutNDProof rtc = toDeductionFitch (parseGamutND rtc) (gamutNDFormulaParser)

gamutNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gamutNDFormulaParser
    , ndParseForm = gamutNDFormulaParser
    , ndNotation = gamutNotation
    }
