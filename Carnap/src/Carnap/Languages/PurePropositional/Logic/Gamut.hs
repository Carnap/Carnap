{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gamut 
    ( GamutMPND, gamutMPNDCalc, parseGamutMPND
    , GamutIPND, gamutIPNDCalc, parseGamutIPND
    , GamutPND, gamutPNDCalc, parseGamutPND
    ) where

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

data GamutMPND = InAnd  | ElimAndL | ElimAndR
               | ElimIf | InIf1    | InIf2
               | InNeg1 | InNeg2   | ElimNeg 
               | ElimOr | InOrL    | InOrR 
               | AS     | PR       | Rep
    deriving Eq

data GamutIPND = MPND GamutMPND | EFSQ
    deriving Eq

data GamutPND = IPND GamutIPND | DNE
    deriving Eq

instance Show GamutMPND where
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
        show AS         = "assumption"
        show PR         = "assumption"
        show Rep        = "repeat"

instance Show GamutIPND where
        show (MPND x)   = show x
        show EFSQ       = "EFSQ"

instance Show GamutPND where
        show (IPND x)   = show x
        show DNE        = "¬¬"

instance Inference GamutMPND PurePropLexicon (Form Bool) where
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
        ruleOf AS         = axiom
        ruleOf PR         = axiom

        indirectInference x
            | x `elem` [InIf1, InIf2, InNeg1, InNeg2] = Just (WithAlternate (ImplicitProof (ProofType 0 1)) (TypedProof (ProofType 0 1)))
            | otherwise = Nothing

        isAssumption AS = True
        isAssumption _ = False

instance Inference GamutIPND PurePropLexicon (Form Bool) where
        ruleOf (MPND x) = ruleOf x
        ruleOf EFSQ     = falsumElimination

        indirectInference (MPND x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (MPND x) = isAssumption x
        isAssumption _ = False

instance Inference GamutPND PurePropLexicon (Form Bool) where
        ruleOf (IPND x) = ruleOf x
        ruleOf DNE = doubleNegationElimination

        indirectInference (IPND x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (IPND x) = isAssumption x
        isAssumption _ = False

parseGamutMPND rtc = do r <- choice (map (try . string) 
                                [ "I∧" , "I/\\", "I^", "E∧" , "E/\\", "E^"
                                , "E→" , "E->", "I→" , "I->"
                                , "I¬" , "I~", "I-", "E¬" , "E~", "E-"
                                , "E∨" , "E\\/", "Ev",  "I∨" , "I\\/", "Iv"
                                , "repetition", "rep" , "assumption", "as"])
                        case r of 
                         r | r `elem` ["I∧" , "I/\\", "I^"] -> return [InAnd]
                           | r `elem` ["E∧" , "E/\\", "E^"] -> return [ElimAndR, ElimAndL]
                           | r `elem` ["E→" , "E->"]        -> return [ElimIf]
                           | r `elem` ["I→" , "I->"]        -> return [InIf1, InIf2]
                           | r `elem` ["I¬" , "I~", "I-"]   -> return [InNeg1, InNeg2]
                           | r `elem` ["E¬" , "E~", "E-"]   -> return [ElimNeg]
                           | r `elem` ["E∨" , "E\\/", "Ev"] -> return [ElimOr]
                           | r `elem` ["I∨" , "I\\/", "Iv"] -> return [InOrL, InOrR]
                           | r `elem` ["repetition", "rep"] -> return [Rep]
                           | r `elem` ["assumption", "as"]  -> return [AS, PR]

parseGamutIPND rtc = (map MPND <$> parseGamutMPND rtc) <|> (try (string "EFSQ") >> return [EFSQ])

parseGamutPND rtc = (map IPND <$> parseGamutIPND rtc) 
                 <|> (choice (map (try . string) ["~~","¬¬","--"]) >> return [DNE])

parseGamutMPNDProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutMPND PurePropLexicon (Form Bool)]
parseGamutMPNDProof rtc = toDeductionFitch (parseGamutMPND rtc) (purePropFormulaParser gamutOpts)

parseGamutIPNDProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutIPND PurePropLexicon (Form Bool)]
parseGamutIPNDProof rtc = toDeductionFitch (parseGamutIPND rtc) (purePropFormulaParser gamutOpts)

parseGamutPNDProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutPND PurePropLexicon (Form Bool)]
parseGamutPNDProof rtc = toDeductionFitch (parseGamutPND rtc) (purePropFormulaParser gamutOpts)

gamutNotation :: String -> String
gamutNotation (x:xs) | isUpper x = toLower x : gamutNotation xs
                     | otherwise = x : gamutNotation xs
gamutNotation [] = []

gamutMPNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutMPNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }

gamutIPNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutIPNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }

gamutPNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutPNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }
