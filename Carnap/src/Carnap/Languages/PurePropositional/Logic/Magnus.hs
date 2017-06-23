{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Magnus
    ( parseForallxSL,  ForallxSL,  forallxSLCalc, ) where

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


--A system for propositional logic resembling the proof system SL from PD
--Magnus' forallx book

data ForallxSL = ReiterateX  | ConjIntroX
               | ConjElim1X  | ConjElim2X
               | DisjIntro1X | DisjIntro2X
               | DisjElim1X  | DisjElim2X
               | CondIntro1X | CondIntro2X
               | CondElimX
               | BicoIntro1X | BicoIntro2X
               | BicoIntro3X | BicoIntro4X
               | BicoElim1X  | BicoElim2X
               | NegeIntro1X | NegeIntro2X
               | NegeIntro3X | NegeIntro4X
               | NegeElim1X  | NegeElim2X
               | NegeElim3X  | NegeElim4X
               | ForXAssump  | ForXPrem
               deriving (Eq)
               --skipping derived rules for now

instance Show ForallxSL where
        show ConjIntroX  = "∧I"
        show ConjElim1X  = "∧E"
        show ConjElim2X  = "∧E"
        show CondIntro1X = "→I"
        show CondIntro2X = "→I"
        show CondElimX   = "→E"
        show NegeIntro1X = "¬I"
        show NegeIntro2X = "¬I"
        show NegeIntro3X = "¬I"
        show NegeIntro4X = "¬I"
        show NegeElim1X  = "¬E" 
        show NegeElim2X  = "¬E"
        show NegeElim3X  = "¬E"
        show NegeElim4X  = "¬E"
        show DisjElim1X  = "∨E"
        show DisjElim2X  = "∨E"
        show DisjIntro1X = "∨I"
        show DisjIntro2X = "∨I"
        show BicoIntro1X = "↔I"
        show BicoIntro2X = "↔I"
        show BicoIntro3X = "↔I"
        show BicoIntro4X = "↔I"
        show BicoElim1X  = "↔E"
        show BicoElim2X  = "↔E"
        show ReiterateX  = "R"
        show ForXAssump  = "AS"
        show ForXPrem    = "PR"

instance Inference ForallxSL PurePropLexicon where
        ruleOf ReiterateX = identityRule
        ruleOf ConjIntroX = adjunction
        ruleOf ConjElim1X = simplificationVariations !! 0
        ruleOf ConjElim2X = simplificationVariations !! 1
        ruleOf DisjIntro1X = additionVariations !! 0
        ruleOf DisjIntro2X = additionVariations !! 1 
        ruleOf DisjElim1X = modusTollendoPonensVariations !! 0
        ruleOf DisjElim2X = modusTollendoPonensVariations !! 1
        ruleOf CondIntro1X = conditionalProofVariations !! 0
        ruleOf CondIntro2X = conditionalProofVariations !! 1
        ruleOf CondElimX = modusPonens
        ruleOf BicoIntro1X = biconditionalProofVariations !! 0
        ruleOf BicoIntro2X = biconditionalProofVariations !! 1
        ruleOf BicoIntro3X = biconditionalProofVariations !! 2
        ruleOf BicoIntro4X = biconditionalProofVariations !! 3
        ruleOf BicoElim1X = biconditionalPonensVariations !! 0
        ruleOf BicoElim2X = biconditionalPonensVariations !! 1
        ruleOf NegeIntro1X = constructiveReductioVariations !! 0
        ruleOf NegeIntro2X = constructiveReductioVariations !! 1
        ruleOf NegeIntro3X = constructiveReductioVariations !! 2
        ruleOf NegeIntro4X = constructiveReductioVariations !! 3
        ruleOf NegeElim1X = nonConstructiveReductioVariations !! 0
        ruleOf NegeElim2X = nonConstructiveReductioVariations !! 1
        ruleOf NegeElim3X = nonConstructiveReductioVariations !! 2
        ruleOf NegeElim4X = nonConstructiveReductioVariations !! 3
        ruleOf ForXAssump = axiom
        ruleOf ForXPrem  = axiom

        indirectInference x
            | x `elem` [CondIntro1X,CondIntro2X, BicoIntro1X, BicoIntro2X
                       , BicoIntro3X, BicoIntro4X ] = Just PolyProof
            | x `elem` [ NegeIntro1X, NegeIntro2X , NegeIntro3X, NegeIntro4X
                       , NegeElim1X, NegeElim2X, NegeElim3X , NegeElim4X
                       ] = Just DoubleProof
            | otherwise = Nothing

        isAssumption ForXAssump = True
        isAssumption _ = False

parseForallxSL :: Map String DerivedRule -> Parsec String u [ForallxSL]
parseForallxSL ders = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I","→E","CE","->E", "→E"
                                                         ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I" 
                                                         , "BE", "<->E", "↔E", "R"])
                         case r of
                             "AS"   -> return [ForXAssump]
                             "PR"   -> return [ForXPrem]
                             "&I"   -> return [ConjIntroX]
                             "&E"   -> return [ConjElim1X, ConjElim2X]
                             "/\\I" -> return [ConjIntroX]
                             "/\\E" -> return [ConjElim1X, ConjElim2X]
                             "∧I"   -> return [ConjIntroX]
                             "∧E"   -> return [ConjElim1X, ConjElim2X]
                             "CI"   -> return [CondIntro1X,CondIntro2X]
                             "CE"   -> return [CondElimX]
                             "->I"  -> return [CondIntro1X,CondIntro2X]
                             "->E"  -> return [CondElimX]
                             "→I"   -> return [CondIntro1X,CondIntro2X]
                             "→E"   -> return [CondElimX]
                             "~I"   -> return [NegeIntro1X, NegeIntro2X, NegeIntro3X, NegeIntro4X]
                             "~E"   -> return [NegeElim1X, NegeElim2X, NegeElim3X, NegeElim4X]
                             "¬I"   -> return [NegeIntro1X, NegeIntro2X, NegeIntro3X, NegeIntro4X]
                             "¬E"   -> return [NegeElim1X, NegeElim2X, NegeElim3X, NegeElim4X]
                             "-I"   -> return [NegeIntro1X, NegeIntro2X, NegeIntro3X, NegeIntro4X]
                             "-E"   -> return [NegeElim1X, NegeElim2X, NegeElim3X, NegeElim4X]
                             "vI"   -> return [DisjIntro1X, DisjIntro2X]
                             "vE"   -> return [DisjElim1X, DisjElim2X]
                             "∨I"   -> return [DisjIntro1X, DisjIntro2X]
                             "∨E"   -> return [DisjElim1X, DisjElim2X]
                             "\\/I" -> return [DisjIntro1X, DisjIntro2X]
                             "\\/E" -> return [DisjElim1X, DisjElim2X]
                             "BI"   -> return [BicoIntro1X, BicoIntro2X, BicoIntro3X, BicoIntro4X]
                             "BE"   -> return [BicoElim1X, BicoElim2X]
                             "<->I" -> return [BicoIntro1X, BicoIntro2X, BicoIntro3X, BicoIntro4X]
                             "<->E" -> return [BicoElim1X, BicoElim2X]
                             "↔I"   -> return [BicoIntro1X, BicoIntro2X, BicoIntro3X, BicoIntro4X]
                             "↔E"   -> return [BicoElim1X, BicoElim2X]
                             "R"    -> return [ReiterateX]

parseForallxSLProof :: Map String DerivedRule -> String -> [DeductionLine ForallxSL PurePropLexicon (Form Bool)]
parseForallxSLProof ders = toDeductionBE (parseForallxSL ders) (purePropFormulaParser extendedLetters)

forallxSLCalc = NaturalDeductionCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseForallxSLProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Nothing
    , ndParseSeq = extendedPropSeqParser
    }
