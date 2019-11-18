{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gamut (GamutPND, gamutPNDCalc, parseGamutPND) where

import Text.Parsec
import Data.Char
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,subst,FirstOrder)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser (parseSeqOver)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules

data GamutPND = InAnd  | ElimAndL | ElimAndR
              | ElimIf | InIf1    | InIf2
              | InNeg1 | InNeg2   | ElimNeg 
              | ElimOr | InOrL    | InOrR 
              | DNE    | EFSQ
              | AS     | PR       | Rep
    deriving Eq

instance Show GamutPND where
        show InAnd      = "I∧"
        show ElimAndL   = "E∧"
        show ElimAndR   = "E∧"
        show ElimIf     = "E→"
        show InIf1      = "I→"
        show InIf2      = "I→"
        show InNeg1     = "I¬"
        show InNeg2     = "I¬"
        show ElimNeg    = "E¬"
        show ElimOr     = "E∨"
        show InOrL      = "I∨" 
        show InOrR      = "I∨"
        show DNE        = "¬¬" 
        show EFSQ       = "EFSQ"
        show AS         = "assumption"
        show PR         = "assumption"
        show Rep        = "repeat"

instance Inference GamutPND PurePropLexicon (Form Bool) where
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
        ruleOf Rep        = identityRule
        ruleOf InOrL      = additionVariations !! 0
        ruleOf InOrR      = additionVariations !! 1
        ruleOf DNE        = doubleNegationElimination
        ruleOf EFSQ       = falsumElimination
        ruleOf AS         = axiom
        ruleOf PR         = axiom

        indirectInference x
            | x `elem` [InIf1, InIf2, InNeg1, InNeg2] = Just (ImplicitProof (ProofType 0 1))
            | otherwise = Nothing

        isAssumption AS = True
        isAssumption _ = False

parseGamutPND rtc = do r <- choice (map (try . string) 
                                [ "I∧" , "I/\\", "I^", "E∧" , "E/\\", "E^"
                                , "E→" , "E->", "I→" , "I->"
                                , "I¬" , "I~", "I-", "E¬" , "E~", "E-"
                                , "E∨" , "E\\/", "Ev",  "I∨" , "I\\/", "Iv"
                                , "¬¬" , "~~", "--", "repetition", "rep"
                                , "EFSQ" , "assumption", "as", "pr"])
                       case r of 
                        r | r `elem` ["I∧" , "I/\\", "I^"] -> return [InAnd]
                          | r `elem` ["E∧" , "E/\\", "E^"] -> return [ElimAndR, ElimAndL]
                          | r `elem` ["E→" , "E->"]        -> return [ElimIf]
                          | r `elem` ["I→" , "I->"]        -> return [InIf1, InIf2]
                          | r `elem` ["I¬" , "I~", "I-"]   -> return [InNeg1, InNeg2]
                          | r `elem` ["E¬" , "E~", "E-"]   -> return [ElimNeg]
                          | r `elem` ["E∨" , "E\\/", "Ev"] -> return [ElimOr]
                          | r `elem` ["I∨" , "I\\/", "Iv"] -> return [InOrL, InOrR]
                          | r `elem` ["¬¬" , "~~", "--"]   -> return [DNE]
                          | r `elem` ["EFSQ"]              -> return [EFSQ]
                          | r `elem` ["repetition", "rep"] -> return [Rep]
                          | r `elem` ["assumption", "as"]  -> return [AS, PR]
                          | r `elem` ["pr"]  -> return [PR]

parseGamutPNDProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutPND PurePropLexicon (Form Bool)]
parseGamutPNDProof rtc = toDeductionFitch (parseGamutPND rtc) (purePropFormulaParser gamutOpts)

gamutNotation :: String -> String
gamutNotation (x:xs) | isUpper x = toLower x : gamutNotation xs
                     | otherwise = x : gamutNotation xs
gamutNotation [] = []

gamutPNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutPNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }
