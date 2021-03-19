{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gallow 
    ( gallowSLCalc, gallowSLPlusCalc, GallowSLCore(..), GallowSL(..), parseGallowSL, parseGallowSLCore) where

import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.Util.LanguageClasses

data GallowSLCore = GallowSLCore ThomasBolducAndZachTFLCore 
      deriving Eq

data GallowSL = GallowSL ThomasBolducAndZachTFL 
      deriving Eq

instance Show GallowSLCore where
        show (GallowSLCore NegeElim)   = "⊥I"
        show (GallowSLCore Indirect1)  = "¬E"
        show (GallowSLCore Indirect2)  = "¬E"
        show (GallowSLCore ContElim)   = "⊥E"
        show (GallowSLCore x) = show x

instance Show GallowSL where
        show (GallowSL (Core NegeElim))   = "⊥I"
        show (GallowSL (Core Indirect1))  = "¬E"
        show (GallowSL (Core Indirect2))  = "¬E"
        show (GallowSL (Core ContElim))   = "⊥E"
        show (GallowSL x) = show x

instance Inference GallowSLCore PurePropLexicon (Form Bool) where
        ruleOf (GallowSLCore x)  = ruleOf x

        indirectInference (GallowSLCore x)  = indirectInference x

        isAssumption (GallowSLCore x) = isAssumption x

        isPremise (GallowSLCore x) = isPremise x

        globalRestriction (Left ded) n (GallowSLCore CondIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (GallowSLCore CondIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (GallowSLCore BicoIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSLCore BicoIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSLCore BicoIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSLCore BicoIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSLCore DisjElim1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSLCore DisjElim2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSLCore DisjElim3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSLCore DisjElim4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSLCore NegeIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (GallowSLCore NegeIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (GallowSLCore Indirect1) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction (Left ded) n (GallowSLCore Indirect2) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

        restriction (GallowSLCore x) = restriction x

instance Inference GallowSL PurePropLexicon (Form Bool) where
        ruleOf (GallowSL x)  = ruleOf x

        indirectInference (GallowSL x)  = indirectInference x

        isAssumption (GallowSL x) = isAssumption x

        isPremise (GallowSL x) = isPremise x

        globalRestriction (Left ded) n (GallowSL (Core CondIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (GallowSL (Core CondIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (GallowSL (Core BicoIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSL (Core BicoIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSL (Core BicoIntro3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSL (Core BicoIntro4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (GallowSL (Core DisjElim1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSL (Core DisjElim2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSL (Core DisjElim3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSL (Core DisjElim4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (GallowSL (Core NegeIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (GallowSL (Core NegeIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (GallowSL (Core Indirect1)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction (Left ded) n (GallowSL (Core Indirect2)) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

        restriction (GallowSL x) = restriction x

parseGallowSLCoreProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GallowSLCore PurePropLexicon (Form Bool)]
parseGallowSLCoreProof rtc = toDeductionFitch (parseGallowSLCore rtc) (purePropFormulaParser thomasBolducZach2019Opts)

parseGallowSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GallowSL PurePropLexicon (Form Bool)]
parseGallowSLProof rtc = toDeductionFitch (parseGallowSL rtc) (purePropFormulaParser thomasBolducZach2019Opts)

parseGallowSLCore :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [GallowSLCore]
parseGallowSLCore rtc = do r <- choice (map (try . string) [ "AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E", "~I","-I", "¬I"
                                                       , "~E","-E", "¬E","->I", ">I", "=>I", "→I","->E", "=>E", ">E", "→E"
                                                       , "vI","\\/I", "|I", "∨I", "vE","\\/E", "|E", "∨E","<->I", "↔I","<->E"
                                                       , "↔E", "R", "⊥I", "!?I", "_|_I", "⊥E", "!?E", "_|_E"])
                           return $ map GallowSLCore $ coreSort r rtc

parseGallowSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [GallowSL]
parseGallowSL rtc = try parseCore <|> parseRest
        where recore (GallowSLCore r) = GallowSL (Core r)
              parseCore = map recore <$> parseGallowSLCore rtc
              parseRest = do r <- choice (map (try . string) [ "AS", "DS", "MT", "DNE", "LEM", "DeM"])
                             return $ map GallowSL $ case r of
                                     r | r == "DS"   -> [DisSyllo1,DisSyllo2]
                                       | r == "MT"   -> [ModTollens]
                                       | r == "DNE"  -> [DoubleNeg]
                                       | r == "LEM"  -> [Lem1,Lem2,Lem3,Lem4]
                                       | r == "DeM"  -> [DeMorgan1,DeMorgan2,DeMorgan3,DeMorgan4]
                                       | otherwise   -> map Core (coreSort r rtc)
              

coreSort r rtc = case r of
          r | r == "AS"   ->  [As]
            | r == "PR" ->  [Pr (problemPremises rtc)]
            | r `elem` ["&I","/\\I","∧I"] ->  [ConjIntro]
            | r `elem` ["&E","/\\E","∧E"] ->  [ConjElim1, ConjElim2]
            | r `elem` ["~I","¬I","-I"]   ->  [NegeIntro1, NegeIntro2]
            | r `elem` ["~E","¬E","-E"]   ->  [Indirect1, Indirect2]
            | r `elem` ["⊥I", "!?I", "_|_I"] -> [NegeElim]
            | r `elem` ["⊥E", "!?E", "_|_E"] -> [ContElim]
            | r `elem` ["->I", ">I", "=>I", "→I"] ->  [CondIntro1,CondIntro2]
            | r `elem` ["->E", ">E", "=>E", "→E"]  ->  [CondElim]
            | r `elem` ["∨I","vI", "|I", "\\/I"] ->  [DisjIntro1, DisjIntro2]
            | r `elem` ["∨E","vE", "|E", "\\/E"] ->  [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
            | r `elem` ["<->I","↔I"] ->  [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
            | r `elem` ["<->E","↔E"]   ->  [BicoElim1, BicoElim2]
            | r == "R" ->  [Reiterate]

gallowSLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseGallowSLCoreProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZach2019Opts)
    , ndParseForm = purePropFormulaParser thomasBolducZach2019Opts
    , ndNotation = dropOuterParens
    }

gallowSLPlusCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseGallowSLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZach2019Opts)
    , ndParseForm = purePropFormulaParser thomasBolducZach2019Opts
    , ndNotation = dropOuterParens
    }
