{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.IchikawaJenkins (ichikawaJenkinsQLTableauCalc,ichikawaJenkinsQLCalc, parseIchikawaJenkinsQL) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Logic.Magnus
import Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
import Carnap.Calculi.Util
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

data IchikawaJenkinsQL = IJSL IchikawaJenkinsSL | QL MagnusQLPlus
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
    isPremise (QL x) = isPremise x

parseIchikawaJenkinsQL rtc = try quantRule <|> liftProp
    where liftProp = do r <- parseIchikawaJenkinsSL (defaultRuntimeDeductionConfig)
                        return (map IJSL r)
          
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I", "=E", "QN", "PR"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> returnQL [MagnusQL UI]
                              | r `elem` ["∀E","AE"] -> returnQL [MagnusQL UE]
                              | r `elem` ["∃I","EI"] -> returnQL [MagnusQL EI]
                              | r `elem` ["∃E","EE"] -> returnQL [MagnusQL EE1, MagnusQL EE2]
                              | r == "PR" -> returnQL [MagnusQL $ Pr (problemPremises rtc)]
                              | r == "=I" -> returnQL [MagnusQL IDI]
                              | r == "=E" -> returnQL [MagnusQL IDE1, MagnusQL IDE2]
                              | r == "QN" -> returnQL [QN1, QN2, QN3, QN4]

          returnQL = return . map QL

parseIchikawaJenkinsQLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine IchikawaJenkinsQL PureLexiconFOL (Form Bool)]
parseIchikawaJenkinsQLProof rtc = toDeductionFitch (parseIchikawaJenkinsQL rtc) magnusFOLFormulaParser

ichikawaJenkinsQLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseIchikawaJenkinsQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver magnusFOLFormulaParser
    , ndParseForm = magnusFOLFormulaParser
    , ndNotation = ndNotation ichikawaJenkinsSLCalc
    }

-------------------------
--  Semantic Tableaux  --
-------------------------

data IchikawaJenkinsQLTableaux = SL IchikawaJenkinsSLTableaux | Exist | NExist | Forall |  NForall
    deriving Eq

instance Show IchikawaJenkinsQLTableaux where
    show (SL x) = show x
    show Exist = "∃"
    show NExist = "¬∃"
    show Forall = "∀"
    show NForall = "¬∀"

parseIchikawaJenkinsQLTableaux :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [IchikawaJenkinsQLTableaux]
parseIchikawaJenkinsQLTableaux rtc = propRule <|> quantRule
    where propRule = map SL <$> parseIchikawaJenkinsSLTableaux rtc
          quantRule = choice . map try $
                        [ stringOpts ["∀","A"] >> return [Forall]
                        , stringOpts ["-∀", "~∀", "¬∀", "-A", "~A", "¬A"] >> return [NForall]
                        , stringOpts ["∃","E"] >> return [Exist]
                        , stringOpts ["-E","~E","¬E","-∃","~∃","¬∃"] >> return [NExist]
                        ]
          stringOpts = choice . map (try . string)

instance CoreInference IchikawaJenkinsQLTableaux PureLexiconFOL (Form Bool) where
        corePremisesOf (SL x) = corePremisesOf x
        corePremisesOf Forall = [ GammaV 1 :+: SA (lall "v" $ \x -> phi 1 x) :+: SA (phi 1 tau) :|-: Bot]
        corePremisesOf NForall = [ GammaV 1 :+: SA (lneg $ phi 1 tau) :|-: Bot]
        corePremisesOf Exist = [ GammaV 1 :+: SA (phi 1 tau) :|-: Bot]
        corePremisesOf NExist = [ GammaV 1 :+: SA (lneg $ lsome "v" $ \x -> phi 1 x) :+: SA (lneg $ phi 1 tau) :|-: Bot]

        coreConclusionOf (SL x) = coreConclusionOf x
        coreConclusionOf Forall = GammaV 1 :+: SA (lall "v" $ \x -> phi 1 x) :|-: Bot
        coreConclusionOf NForall = GammaV 1 :+: SA (lneg $ lall "v" $ \x -> phi 1 x) :|-: Bot
        coreConclusionOf Exist = GammaV 1 :+: SA (lsome "v" $ \x -> phi 1 x) :|-: Bot
        coreConclusionOf NExist = GammaV 1 :+: SA (lneg $ lsome "v" $ \x -> phi 1 x) :|-: Bot

        coreRestriction (SL x) = coreRestriction x
        coreRestriction Exist = Just (eigenConstraint tau (SS (lsome "v" $ \x -> phi 1 x)) (fogamma 1))
        coreRestriction NForall = Just (eigenConstraint tau (SS (lneg $ lall "v" $ \x -> phi 1 x)) (fogamma 1))
        coreRestriction _ = Nothing

instance SpecifiedUnificationType IchikawaJenkinsQLTableaux where
    unificationType (SL Struct) = ACUIUnification
    unificationType _ = AssociativeUnification

ichikawaJenkinsQLTableauCalc = mkTBCalc
    { tbParseForm = magnusFOLFormulaParser
    , tbParseRule = parseIchikawaJenkinsQLTableaux
    }
