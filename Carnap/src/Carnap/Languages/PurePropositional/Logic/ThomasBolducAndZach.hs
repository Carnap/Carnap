{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach
    ( parseThomasBolducAndZachTFL, ThomasBolducAndZachTFL,  thomasBolducAndZachTFLCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

{-| A system for propositional logic resembling the basic proof system TFL
from the Calgary Remix of Forall x book
-}

data ThomasBolducAndZachTFL = Reiterate  | ConjIntro
              | ConjElim1  | ConjElim2
              | DisjIntro1 | DisjIntro2
              | DisjElim1  | DisjElim2
              | DisjElim3  | DisjElim4
              | CondIntro1 | CondIntro2
              | CondElim
              | BicoIntro1 | BicoIntro2
              | BicoIntro3 | BicoIntro4
              | BicoElim1  | BicoElim2
              | NegeIntro1 | NegeIntro2
              | Tertium1   | Tertium2
              | Tertium3   | Tertium4
              | ContIntro  | ContElim 
              | As         | Pr
              deriving (Eq)
              --skipping derived rules for now

instance Show ThomasBolducAndZachTFL where
        show ConjIntro  = "∧I"
        show ConjElim1  = "∧E"
        show ConjElim2  = "∧E"
        show CondIntro1 = "→I"
        show CondIntro2 = "→I"
        show CondElim   = "→E"
        show NegeIntro1 = "¬I"
        show NegeIntro2 = "¬I"
        show ContIntro  = "⊥I"
        show ContElim   = "⊥E"
        show DisjElim1  = "∨E"
        show DisjElim2  = "∨E"
        show DisjElim3  = "∨E"
        show DisjElim4  = "∨E"
        show DisjIntro1 = "∨I"
        show DisjIntro2 = "∨I"
        show BicoIntro1 = "↔I"
        show BicoIntro2 = "↔I"
        show BicoIntro3 = "↔I"
        show BicoIntro4 = "↔I"
        show BicoElim1  = "↔E"
        show BicoElim2  = "↔E"
        show As         = "AS"
        show Pr         = "PR"
        show Tertium1   = "TND"
        show Tertium2   = "TND"
        show Tertium3   = "TND"
        show Tertium4   = "TND"

instance Inference ThomasBolducAndZachTFL PurePropLexicon where
        ruleOf ConjIntro  = adjunction
        ruleOf ConjElim1  = simplificationVariations !! 0
        ruleOf ConjElim2  = simplificationVariations !! 1
        ruleOf DisjIntro1 = additionVariations !! 0
        ruleOf DisjIntro2 = additionVariations !! 1 
        ruleOf DisjElim1   = proofByCasesVariations !! 0
        ruleOf DisjElim2   = proofByCasesVariations !! 1
        ruleOf DisjElim3   = proofByCasesVariations !! 2
        ruleOf DisjElim4   = proofByCasesVariations !! 3
        ruleOf CondIntro1 = conditionalProofVariations !! 0
        ruleOf CondIntro2 = conditionalProofVariations !! 1
        ruleOf CondElim   = modusPonens
        ruleOf BicoIntro1 = biconditionalProofVariations !! 0
        ruleOf BicoIntro2 = biconditionalProofVariations !! 1
        ruleOf BicoIntro3 = biconditionalProofVariations !! 2
        ruleOf BicoIntro4 = biconditionalProofVariations !! 3
        ruleOf BicoElim1  = biconditionalPonensVariations !! 0
        ruleOf BicoElim2  = biconditionalPonensVariations !! 1
        ruleOf NegeIntro1 = explicitConstructiveFalsumReductioVariations !! 0
        ruleOf NegeIntro2 = explicitConstructiveFalsumReductioVariations !! 1
        ruleOf ContIntro  = falsumIntroduction
        ruleOf ContElim   = falsumElimination
        ruleOf Tertium1   = tertiumNonDaturVariations !! 1
        ruleOf Tertium2   = tertiumNonDaturVariations !! 2
        ruleOf Tertium3   = tertiumNonDaturVariations !! 3
        ruleOf Tertium4   = tertiumNonDaturVariations !! 4
        ruleOf As         = axiom
        ruleOf Pr         = axiom

        indirectInference x
            | x `elem` [ DisjElim1, DisjElim2, DisjElim3, DisjElim4
                       , CondIntro1, CondIntro2
                       , BicoIntro1, BicoIntro2 , BicoIntro3, BicoIntro4
                       , Tertium1, Tertium2, Tertium3, Tertium4
                       ] = Just PolyProof
            | x `elem` [NegeIntro1, NegeIntro2] = Just assumptiveProof
            | otherwise = Nothing

        isAssumption As = True
        isAssumption _  = False

parseThomasBolducAndZachTFL :: Map String DerivedRule -> Parsec String u [ThomasBolducAndZachTFL]
parseThomasBolducAndZachTFL ders = do r <- choice (map (try . string) [ "AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I","→E","CE","->E", "→E"
                                                                      , "~I","-I", "¬I", "vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I", "BE", "<->E"
                                                                      , "↔E", "R", "TND"])
                                      case r of
                                           "AS"   -> return [As]
                                           "PR"   -> return [Pr]
                                           "&I"   -> return [ConjIntro]
                                           "&E"   -> return [ConjElim1, ConjElim2]
                                           "/\\I" -> return [ConjIntro]
                                           "/\\E" -> return [ConjElim1, ConjElim2]
                                           "∧I"   -> return [ConjIntro]
                                           "∧E"   -> return [ConjElim1, ConjElim2]
                                           "CI"   -> return [CondIntro1,CondIntro2]
                                           "CE"   -> return [CondElim]
                                           "->I"  -> return [CondIntro1,CondIntro2]
                                           "->E"  -> return [CondElim]
                                           "→I"   -> return [CondIntro1,CondIntro2]
                                           "→E"   -> return [CondElim]
                                           "~I"   -> return [NegeIntro1, NegeIntro2]
                                           "¬I"   -> return [NegeIntro1, NegeIntro2]
                                           "-I"   -> return [NegeIntro1, NegeIntro2]
                                           "vI"   -> return [DisjIntro1, DisjIntro2]
                                           "vE"   -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                           "\\/I" -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                           "\\/E" -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                           "BI"   -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                           "BE"   -> return [BicoElim1, BicoElim2]
                                           "<->I" -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                           "<->E" -> return [BicoElim1, BicoElim2]
                                           "↔I"   -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                           "↔E"   -> return [BicoElim1, BicoElim2]
                                           "R"    -> return [Reiterate]
                                           "TND"  -> return [Tertium1, Tertium2, Tertium3, Tertium4]

parseThomasBolducAndZachTFLProof :: Map String DerivedRule -> String -> [DeductionLine ThomasBolducAndZachTFL PurePropLexicon (Form Bool)]
parseThomasBolducAndZachTFLProof ders = toDeductionFitch (parseThomasBolducAndZachTFL ders) (purePropFormulaParser extendedLetters)

thomasBolducAndZachTFLCalc = NaturalDeductionCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseThomasBolducAndZachTFLProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Nothing
    , ndParseSeq = extendedPropSeqParser
    }
