{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.EbelsDuggan (ebelsDugganFOLCalc,parseEbelsDugganFOL) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)
import Carnap.Languages.PureFirstOrder.Logic.ThomasBolducAndZach
import Carnap.Languages.PurePropositional.Logic.EbelsDuggan

data EbelsDugganFOL = EDTFL P.EbelsDugganTFL | TBZFOL ThomasBolducAndZachFOL | EQS | EQT

instance Show EbelsDugganFOL where
        show (EDTFL x) = show x
        show (TBZFOL x) = show x
        show EQS = "=S"
        show EQT = "=T"

instance Inference EbelsDugganFOL PureLexiconFOL (Form Bool) where

         ruleOf (TBZFOL x) = ruleOf x
         ruleOf r@(EDTFL x) = premisesOf r ∴ conclusionOf r
         ruleOf EQS = eqSymmetry
         ruleOf EQT = eqTransitivity

         premisesOf (EDTFL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (EDTFL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (EDTFL x) = indirectInference x
         indirectInference (TBZFOL x) = indirectInference x
         indirectInference x = Nothing

         restriction (TBZFOL x) = restriction x
         restriction _     = Nothing

         isAssumption (EDTFL x) = isAssumption x
         isAssumption (TBZFOL x) = isAssumption x
         isAssumption _ = False

         isPremise (EDTFL x) = isPremise x
         isPremise (TBZFOL x) = isPremise x
         isPremise _ = False

parseEbelsDugganFOL rtc = try (map TBZFOL <$> parseThomasBolducAndZachFOL rtc) 
                      <|> try (map EDTFL <$> parseEbelsDugganTFL (defaultRuntimeDeductionConfig))
                      <|> do r <- choice (map (try . string) ["=S", "=T"])
                             return $ case r of "=S" -> [EQS]
                                                "=T" -> [EQT]

parseEbelsDugganFOLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine EbelsDugganFOL PureLexiconFOL (Form Bool)]
parseEbelsDugganFOLProof ders = toDeductionFitch (parseEbelsDugganFOL ders) thomasBolducAndZachFOLFormulaParser

ebelsDugganFOLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseEbelsDugganFOLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOLFormulaParser
    , ndParseForm = thomasBolducAndZachFOLFormulaParser
    , ndNotation = ndNotation P.thomasBolducAndZachTFLCalc
    }
