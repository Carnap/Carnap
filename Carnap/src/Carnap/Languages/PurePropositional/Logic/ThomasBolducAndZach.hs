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

data ThomasBolducAndZachTFL = ConjIntro
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
                            | NegeElim   | ContElim 
                            | Indirect1  | Indirect2
                            | As         | Pr
                            deriving (Eq)
                            --skipping derived rules for now

instance Show ThomasBolducAndZachTFL where
        show ConjIntro  = "∧I"
        show ConjElim1  = "∧E"
        show ConjElim2  = "∧E"
        show NegeIntro1 = "¬I"
        show NegeIntro2 = "¬I"
        show NegeElim   = "¬I"
        show Indirect1  = "IP"
        show Indirect2  = "IP"
        show CondIntro1 = "→I"
        show CondIntro2 = "→I"
        show CondElim   = "→E"
        show ContElim   = "X"
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

instance Inference ThomasBolducAndZachTFL PurePropLexicon (Form Bool) where
        ruleOf ConjIntro  = adjunction
        ruleOf ConjElim1  = simplificationVariations !! 0
        ruleOf ConjElim2  = simplificationVariations !! 1
        ruleOf NegeIntro1 = explicitConstructiveFalsumReductioVariations !! 0
        ruleOf NegeIntro2 = explicitConstructiveFalsumReductioVariations !! 1
        ruleOf NegeElim   = falsumIntroduction
        ruleOf Indirect1  = explicitNonConstructiveFalsumReductioVariations !! 0
        ruleOf Indirect2  = explicitNonConstructiveFalsumReductioVariations !! 1
        ruleOf CondIntro1 = conditionalProofVariations !! 0
        ruleOf CondIntro2 = conditionalProofVariations !! 1
        ruleOf ContElim   = falsumElimination
        ruleOf DisjIntro1 = additionVariations !! 0
        ruleOf DisjIntro2 = additionVariations !! 1 
        ruleOf DisjElim1  = proofByCasesVariations !! 0
        ruleOf DisjElim2  = proofByCasesVariations !! 1
        ruleOf DisjElim3  = proofByCasesVariations !! 2
        ruleOf DisjElim4  = proofByCasesVariations !! 3
        ruleOf BicoIntro1 = biconditionalProofVariations !! 0
        ruleOf BicoIntro2 = biconditionalProofVariations !! 1
        ruleOf BicoIntro3 = biconditionalProofVariations !! 2
        ruleOf BicoIntro4 = biconditionalProofVariations !! 3
        ruleOf BicoElim1  = biconditionalPonensVariations !! 0
        ruleOf BicoElim2  = biconditionalPonensVariations !! 1
        ruleOf As         = axiom
        ruleOf Pr         = axiom

        indirectInference x
            | x `elem` [ DisjElim1, DisjElim2, DisjElim3, DisjElim4
                       , CondIntro1, CondIntro2 , BicoIntro1, BicoIntro2
                       , BicoIntro3, BicoIntro4] = Just PolyProof
            | x `elem` [ NegeIntro1, NegeIntro2
                       , Indirect1, Indirect2] = Just assumptiveProof
            | otherwise = Nothing

        isAssumption As = True
        isAssumption _  = False

parseThomasBolducAndZachTFL :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [ThomasBolducAndZachTFL]
parseThomasBolducAndZachTFL ders = do r <- choice (map (try . string) [ "AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E", "~I","-I", "¬I","IP","->I","→I","→E","->E", "→E"
                                                                      ,"X", "vI","\\/I","∨I", "vE","\\/E", "∨E","<->I", "↔I","<->E" , "↔E"])
                                      case r of
                                           "AS"   -> return [As]
                                           "PR"   -> return [Pr]
                                           "&I"   -> return [ConjIntro]
                                           "/\\I" -> return [ConjIntro]
                                           "∧I"   -> return [ConjIntro]
                                           "&E"   -> return [ConjElim1, ConjElim2]
                                           "/\\E" -> return [ConjElim1, ConjElim2]
                                           "∧E"   -> return [ConjElim1, ConjElim2]
                                           "~I"   -> return [NegeIntro1, NegeIntro2]
                                           "¬I"   -> return [NegeIntro1, NegeIntro2]
                                           "-I"   -> return [NegeIntro1, NegeIntro2]
                                           "~E"   -> return [NegeElim]
                                           "¬E"   -> return [NegeElim]
                                           "-E"   -> return [NegeElim]
                                           "IP"   -> return [Indirect1, Indirect2]
                                           "->I"  -> return [CondIntro1,CondIntro2]
                                           "→I"   -> return [CondIntro1,CondIntro2]
                                           "->E"  -> return [CondElim]
                                           "→E"   -> return [CondElim]
                                           "X"    -> return [ContElim]
                                           "∨I"   -> return [DisjIntro1, DisjIntro2]
                                           "vI"   -> return [DisjIntro1, DisjIntro2]
                                           "\\/I" -> return [DisjIntro1, DisjIntro2]
                                           "∨E"   -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                           "vE"   -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                           "\\/E" -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                           "<->I" -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                           "↔I"   -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                           "<->E" -> return [BicoElim1, BicoElim2]
                                           "↔E"   -> return [BicoElim1, BicoElim2]

parseThomasBolducAndZachTFLProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine ThomasBolducAndZachTFL PurePropLexicon (Form Bool)]
parseThomasBolducAndZachTFLProof ders = toDeductionFitch (parseThomasBolducAndZachTFL ders) (purePropFormulaParser $ extendedLetters {hasBooleanConstants = True})

thomasBolducAndZachTFLCalc = NaturalDeductionCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseThomasBolducAndZachTFLProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Nothing
    , ndParseSeq = extendedPropSeqParser
    }
