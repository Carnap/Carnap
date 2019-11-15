{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}

import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,subst,FirstOrder)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser (parseSeqOver)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules

data GamutND = InAnd  | ElimAndL | ElimAndR
             | ElimIf | InIf1    | InIf2
             | InNeg1 | InNeg2   | ElimNeg 
             | ElimOr | InOrL    | InOrR 
             | DNE    | EFSQ
             | AS 

instance Show GamultND where
        show InAnd      = "I∧"
        show ElimAndL   = "E∧"
        show ElimAndR   = "E∧"
        show ElimIf     = "E→"
        show InIf1      = "I→"
        show InIf2      = "I→"
        show InNeg      = "I¬"
        show ElimNeg    = "E¬"
        show ElimOr     = "E∨"
        show InOrL      = "I∨" 
        show InOrR      = "I∨"
        show DNE        = "¬¬" 
        show EFSQ       = "EFSQ"
        show AS         = "assumption"

instance Inference GamutND PureLexiconFOL (Form Bool) where
        ruleOf InAnd      = adjunction
        ruleOf ElimAndL   = simplificationVariations !! 0
        ruleOf ElimAndR   = simplificationVariations !! 1
        ruleOf ElimIf     = modusPonens
        ruleOf InIf1      = conditionalProofVariations !! 0
        ruleOf InIf2      = conditionalProofVariations !! 1
        ruleOf InNeg1     = constructiveFalsumReductioVariations !! 0
        ruleOf InNeg2     = constructiveFalsumReductioVariations !! 1
        ruleOf ElimNeg    = falsumIntroduction
        ruleOf ElimOr     = dilemma
        ruleOf InOrL      = additionVariations !! 0
        ruleOf InOrR      = additionVariations !! 1
        ruleOf DNE        = doubleNegationElimination
        ruleOf EFSQ       = falusmElimination
        ruleOf AS         = axiom

        indirectInference x
            | x `elem` [InIf1, InIf2, InNeg1, InNeg2] = Just PolyProof
            | otherwise = Nothing

        isAssumption AS = True
        isAssumption _ = False
