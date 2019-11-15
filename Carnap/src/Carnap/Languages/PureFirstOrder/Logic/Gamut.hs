{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gamut (gamutNDCalc, parseGamutND) where

import Text.Parsec
import Data.Char
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
    deriving Eq

instance Show GamutND where
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
        ruleOf EFSQ       = falsumElimination
        ruleOf AS         = axiom

        indirectInference x
            | x `elem` [InIf1, InIf2, InNeg1, InNeg2] = Just PolyProof
            | otherwise = Nothing

        isAssumption AS = True
        isAssumption _ = False


parseGamutND rtc = do r <- choice (map (try . string) 
                                [ "I∧" , "I/\\", "I^", "E∧" , "E/\\", "E^"
                                , "E→" , "E->", "I→" , "I->"
                                , "I¬" , "I~", "I-", "E¬" , "E~", "E-"
                                , "E∨" , "E\\/", "Ev",  "I∨" , "I\\/", "Iv"
                                , "¬¬" , "~~", "--"
                                , "EFSQ" , "assumption", "as"])
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
                          | r `elem`  ["assumption", "as"] -> return [AS]

parseGamutNDProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GamutND PureLexiconFOL (Form Bool)]
parseGamutNDProof rtc = toDeductionFitch (parseGamutND rtc) (gamutNDFormulaParser)

gamutNotation :: String -> String
gamutNotation (x:y:xs) | isUpper x && (y == '(') = x : gamutNotation xs 
                       | isUpper x = toLower x : y : gamutNotation xs
                       | x == ')'  = y : gamutNotation xs
                       | otherwise = x : gamutNotation (y : xs)
gamutNotation (x:[])   | isUpper x = toLower x:[]
                       | x == ')'  = []
gamutNotation x = x


gamutNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gamutNDFormulaParser
    , ndParseForm = gamutNDFormulaParser
    , ndNotation = gamutNotation
    }
