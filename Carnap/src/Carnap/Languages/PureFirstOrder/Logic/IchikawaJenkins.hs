{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.IchikawaJenkins (ichikawaJenkinsQLCalc, parseIchikawaJenkinsQL) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

data IchikawaJenkinsQL = IJSL IchikawaJenkinsSL | QL MagnusQL
        deriving Eq

instance Show IchikawaJenkinsQL where
        show (IJSL x) = show x
        show (QL x) = show x

instance Inference IchikawaJenkinsQL PureLexiconFOL (Form Bool) where

    ruleOf (QL x) = ruleOf x

    premisesOf (IJSL x) = map liftSequent (premisesOf x)
    premisesOf r = upperSequents (ruleOf r)

    conclusionOf (IJSL x) = liftSequent (conclusionOf x)
    conclusionOf r = lowerSequent (ruleOf r)

    indirectInference (IJSL x) = indirectInference x
    indirectInference (QL x) = indirectInference x

    restriction (QL x) = restriction x
    --XXX: handle stricter eigenconstraint here
    restriction _ = Nothing 

    isAssumption (IJSL x) = isAssumption x
    isAssumption _ = False

    isPremise (IJSL x) = isPremise x
    isPremise _ = False

parseIchikawaJenkinsQL rtc = try quantRule <|> liftProp
    where liftProp = do r <- parseIchikawaJenkinsSL (RuntimeNaturalDeductionConfig mempty mempty)
                        return (map IJSL r)
          
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E","PR"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> returnQL [UI]
                              | r `elem` ["∀E","AE"] -> returnQL [UE]
                              | r `elem` ["∃I","EI"] -> returnQL [EI]
                              | r `elem` ["∃E","EE"] -> returnQL [EE1, EE2]
                              | r == "PR" -> returnQL [Pr (problemPremises rtc)]
                              | r == "=I" -> returnQL [IDI]
                              | r == "=E" -> returnQL [IDE1,IDE2]

          returnQL = return . map QL

parseIchikawaJenkinsQLProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine IchikawaJenkinsQL PureLexiconFOL (Form Bool)]
parseIchikawaJenkinsQLProof rtc = toDeductionFitch (parseIchikawaJenkinsQL rtc) magnusFOLFormulaParser

ichikawaJenkinsQLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseIchikawaJenkinsQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver magnusFOLFormulaParser
    , ndNotation = ndNotation ichikawaJenkinsSLCalc
    }
