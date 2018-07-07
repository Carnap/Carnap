{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
    (parseFitchPropLogic, parseFitchPropProof, LogicBookSD,
     logicBookCalc) where

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



--A system for propositional logic resembling the proof system SD from
--Bergmann, Moor and Nelson's Logic Book

data LogicBookSD = ConjIntro  
                        | ConjElim1  | ConjElim2
                        | CondIntro1 | CondIntro2
                        | CondElim
                        | NegeIntro1 | NegeIntro2
                        | NegeIntro3 | NegeIntro4
                        | NegeElim1  | NegeElim2
                        | NegeElim3  | NegeElim4
                        | DisjIntro1 | DisjIntro2
                        | DisjElim1  | DisjElim2
                        | DisjElim3  | DisjElim4
                        | BicoIntro1 | BicoIntro2 
                        | BicoIntro3 | BicoIntro4
                        | BicoElim1  | BicoElim2
                        | Reiterate  | LBAS
                        | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               deriving Eq

instance Show LogicBookSD where
        show ConjIntro  = "∧I"
        show ConjElim1  = "∧E"
        show ConjElim2  = "∧E"
        show CondIntro1 = "→I"
        show CondIntro2 = "→I"
        show CondElim   = "→E"
        show NegeIntro1 = "¬I"
        show NegeIntro2 = "¬I"
        show NegeIntro3 = "¬I"
        show NegeIntro4 = "¬I"
        show NegeElim1  = "¬E" 
        show NegeElim2  = "¬E"
        show NegeElim3  = "¬E"
        show NegeElim4  = "¬E"
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
        show Reiterate  = "R"
        show (Pr _)     = "PR"
        show LBAS       = "AS"

instance Inference LogicBookSD PurePropLexicon (Form Bool) where
    ruleOf Reiterate  = identityRule
    ruleOf CondElim   = modusPonens
    ruleOf CondIntro1 = conditionalProofVariations !! 0 
    ruleOf CondIntro2 = conditionalProofVariations !! 1
    ruleOf ConjIntro  = adjunction
    ruleOf NegeIntro1 = constructiveReductioVariations !! 0
    ruleOf NegeIntro2 = constructiveReductioVariations !! 1
    ruleOf NegeIntro3 = constructiveReductioVariations !! 2
    ruleOf NegeIntro4 = constructiveReductioVariations !! 3
    ruleOf NegeElim1  = nonConstructiveReductioVariations !! 0
    ruleOf NegeElim2  = nonConstructiveReductioVariations !! 1
    ruleOf NegeElim3  = nonConstructiveReductioVariations !! 2
    ruleOf NegeElim4  = nonConstructiveReductioVariations !! 3
    ruleOf DisjIntro1 = additionVariations !! 0
    ruleOf DisjIntro2 = additionVariations !! 1
    ruleOf DisjElim1  = proofByCasesVariations !! 0
    ruleOf DisjElim2  = proofByCasesVariations !! 1
    ruleOf DisjElim3  = proofByCasesVariations !! 2
    ruleOf DisjElim4  = proofByCasesVariations !! 3
    ruleOf ConjElim1  = simplificationVariations !! 0
    ruleOf ConjElim2  = simplificationVariations !! 1
    ruleOf BicoIntro1 = biconditionalProofVariations !! 0
    ruleOf BicoIntro2 = biconditionalProofVariations !! 1
    ruleOf BicoIntro3 = biconditionalProofVariations !! 2
    ruleOf BicoIntro4 = biconditionalProofVariations !! 3
    ruleOf (Pr _)     = axiom
    ruleOf LBAS       = axiom
    ruleOf BicoElim1  = biconditionalPonensVariations !! 0
    ruleOf BicoElim2  = biconditionalPonensVariations !! 1

    indirectInference x
        | x `elem` [CondIntro1,CondIntro2, BicoIntro1, BicoIntro2
                   , BicoIntro3, BicoIntro4 , DisjElim1, DisjElim2
                   , DisjElim3, DisjElim4 ] = Just PolyProof
        | x `elem` [ NegeIntro1, NegeIntro2 , NegeIntro3, NegeIntro4
                   , NegeElim1, NegeElim2, NegeElim3, NegeElim4
                   ] = Just doubleProof
        | otherwise = Nothing

    isAssumption LBAS = True
    isAssumption _ = False

    restriction (Pr prems) = Just (premConstraint prems)
    restriction _ = Nothing

parseFitchPropLogic :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [LogicBookSD]
parseFitchPropLogic rtc = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I","→E","CE","->E", "→E"
                                                              ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I" 
                                                              , "BE", "<->E", "↔E", "R"])
                             case r of
                               r | r == "AS" -> return [LBAS]
                                 | r == "PR" -> return [Pr (problemPremises rtc)]
                                 | r == "R"    -> return [Reiterate]
                                 | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                                 | r `elem` ["&E","/\\E","∧E"] -> return [ConjElim1, ConjElim2]
                                 | r `elem` ["CI","->I","→I"] -> return [CondIntro1,CondIntro2]
                                 | r `elem` ["CE","->E","→E"] -> return [CondElim]
                                 | r `elem` ["~I","¬I","-I"]  -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                                 | r `elem` ["~E","¬E","-E"]  -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                                 | r `elem` ["vI","\\/I"] -> return [DisjIntro1, DisjIntro2]
                                 | r `elem` ["vE","\\/E"] -> return [DisjElim1, DisjElim2,DisjElim3, DisjElim4]
                                 | r `elem` ["BI","<->I","↔I"] -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                 | r `elem` ["BE","<->E","↔E"] -> return [BicoElim1, BicoElim2]

parseFitchPropProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine LogicBookSD PurePropLexicon (Form Bool)]
parseFitchPropProof ders = toDeductionFitch (parseFitchPropLogic ders) (purePropFormulaParser extendedLetters)

logicBookCalc = NaturalDeductionCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseFitchPropProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Nothing
    , ndParseSeq = extendedPropSeqParser
    }
