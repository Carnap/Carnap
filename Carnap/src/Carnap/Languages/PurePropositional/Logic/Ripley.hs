{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Ripley
    (parseRipleyLNJ, RipleyLNJ, ripleyLNJCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

{-| A system for intuitionistic propositional logic resembling Gentzen's NJ, only Lemmon-style
-}

data RipleyLNJ = ConjIntro
               | ConjElimL  | ConjElimR
               | CondIntro  | CondElim
               | DisjIntroL | DisjIntroR
               | DisjElim   
               | As
--               | BotElim
--               | NegIntro   | NegElim
               deriving (Eq)

-- For now, holding off on bot, and so on negation. Dunno how to make new rules.

instance Show RipleyLNJ where
        show ConjIntro  = "∧I"
        show ConjElimL  = "∧EL"
        show ConjElimR  = "∧ER"
        show CondIntro  = "→I"
        show CondElim   = "→E"
        show DisjIntroL = "∨IL"
        show DisjIntroR = "∨IR"
        show DisjElim   = "∨E"
        show As         = "AS"
--        show BotElim    = "⊥E"
--        show NegIntro   = "¬I"
--        show NegElim    = "¬E"


instance Inference RipleyLNJ PurePropLexicon (Form Bool) where
        ruleOf ConjIntro  = adjunction
        ruleOf ConjElimL  = simplificationVariations !! 0
        ruleOf ConjElimR  = simplificationVariations !! 1
        ruleOf CondIntro  = conditionalProofVariations !! 0
        ruleOf CondElim   = modusPonens
        ruleOf DisjIntroL = additionVariations !! 1
        ruleOf DisjIntroR = additionVariations !! 0
        ruleOf DisjElim   = proofByCasesVariations !! 0
        ruleOf As         = axiom        

        indirectInference x
           | x `elem` [CondIntro, DisjElim] = Just PolyProof
           | otherwise = Nothing

        isAssumption As = True
        isAssumption _  = False

        restriction  _     = Nothing

parseRipleyLNJ rtc n _ = do 
                         r <- choice (map (try . string) 
                           [ "AS"
                           , "&I" , "/\\I" , "∧I"
                           , "&EL", "/\\EL", "∧EL"
                           , "&ER", "/\\ER", "∧ER"
                           , "->I", "→I"
                           , "->E", "→E"
                           , "vIL", "\\/IL", "∨IL"
                           , "vIR", "\\/IR", "∨IR"
                           , "vE" ,"\\/E"  , "∨E"
                           ])
                         case r of
                              r | r == "AS"   -> return [As]
                                | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                                | r `elem` ["&EL","/\\EL","∧EL"] -> return [ConjElimL]
                                | r `elem` ["&ER","/\\ER","∧ER"] -> return [ConjElimR]
                                | r `elem` ["->I", "→I"] -> return [CondIntro]
                                | r `elem` ["->E","→E"]  -> return [CondElim]
                                | r `elem` ["∨IL","vIL","\\/IL"] -> return [DisjIntroL]
                                | r `elem` ["∨IR","vIR","\\/IR"] -> return [DisjIntroR]
                                | r `elem` ["∨E","vE","\\/E"] -> return [DisjElim]

  
parseRipleyLNJProof ::  RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine RipleyLNJ PurePropLexicon (Form Bool)]
parseRipleyLNJProof rtc = toDeductionLemmon (parseRipleyLNJ rtc) (purePropFormulaParser ripleyOpts)

ripleyLNJCalc :: NaturalDeductionCalc RipleyLNJ PurePropLexicon (Form Bool)
ripleyLNJCalc = mkNDCalc
    { ndRenderer = LemmonStyle StandardLemmon
    , ndParseProof = parseRipleyLNJProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    }

