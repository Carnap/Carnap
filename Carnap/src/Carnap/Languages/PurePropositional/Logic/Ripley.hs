{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Ripley
    (parseRipleyLNJ, RipleyLNJ, ripleyLNJCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes (lhs)
import Control.Lens (view)
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

data RipleyLNJ = ConjIntro  | ConjElimL    | ConjElimR
               | CondIntro  | CondIntroVac | CondElim
               | DisjIntroL | DisjIntroR   | DisjElim   
               | As         | FalsumElim      
               deriving (Eq)

instance Show RipleyLNJ where
        show ConjIntro    = "∧I"
        show ConjElimL    = "∧EL"
        show ConjElimR    = "∧ER"
        show CondIntro    = "→I"
        show CondIntroVac = "→Iv"
        show CondElim     = "→E"
        show DisjIntroL   = "∨IL"
        show DisjIntroR   = "∨IR"
        show DisjElim     = "∨E"
        show FalsumElim   = "⊥E"
        show As           = "AS"

instance Inference RipleyLNJ PurePropLexicon (Form Bool) where
        ruleOf ConjIntro    = adjunction
        ruleOf ConjElimL    = simplificationVariations !! 0
        ruleOf ConjElimR    = simplificationVariations !! 1
        ruleOf CondIntro    = explicitConditionalProofVariations !! 0
        ruleOf CondIntroVac = explicitConditionalProofVariations !! 1
        ruleOf CondElim     = modusPonens
        ruleOf DisjIntroL   = additionVariations !! 1
        ruleOf DisjIntroR   = additionVariations !! 0
        ruleOf DisjElim     = explicitProofByCasesVariations !! 0
        ruleOf FalsumElim   = falsumElimination
        ruleOf As           = axiom        

        globalRestriction (Left ded) n CondIntro = Just (dischargeConstraint n ded (view lhs $ conclusionOf CondIntro))
        globalRestriction (Left ded) n CondIntroVac = Just (dischargeConstraint n ded (view lhs $ conclusionOf CondIntroVac))
        globalRestriction (Left ded) n DisjElim = Just (dischargeConstraint n ded (view lhs $ conclusionOf DisjElim))
        globalRestriction _ _ _ = Nothing

        indirectInference CondIntro = Just $ TypedProof (ProofType 1 1)
        indirectInference DisjElim = Just $ TypedProof (ProofType 2 1)
        indirectInference _ = Nothing

        isAssumption As = True
        isAssumption _  = False

        restriction  _     = Nothing

parseRipleyLNJ rtc n _ = do 
                         r <- choice (map (try . string) 
                           [ "AS"
                           , "&I" , "/\\I" , "∧I"
                           , "&EL", "/\\EL", "∧EL"
                           , "&ER", "/\\ER", "∧ER"
                           , "->Iv"
                           , "->I", "→I"
                           , "->E", "→E"
                           , "vIL", "\\/IL", "∨IL"
                           , "vIR", "\\/IR", "∨IR"
                           , "vE" ,"\\/E"  , "∨E"
                           , "⊥E", "_|_E", "falsumE"
                           ])
                         case r of
                              r | r == "AS"   -> return [As]
                                | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                                | r `elem` ["&EL","/\\EL","∧EL"] -> return [ConjElimL]
                                | r `elem` ["&ER","/\\ER","∧ER"] -> return [ConjElimR]
                                | r `elem` ["->I", "→I"] -> return [CondIntro, CondIntroVac]
                                | r `elem` ["->Iv"] -> return [CondIntroVac]
                                | r `elem` ["->E","→E"]  -> return [CondElim]
                                | r `elem` ["∨IL","vIL","\\/IL"] -> return [DisjIntroL]
                                | r `elem` ["∨IR","vIR","\\/IR"] -> return [DisjIntroR]
                                | r `elem` ["∨E","vE","\\/E"] -> return [DisjElim]
                                | r `elem` ["⊥E", "_|_E", "falsumE"] -> return [FalsumElim]

  
parseRipleyLNJProof ::  RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine RipleyLNJ PurePropLexicon (Form Bool)]
parseRipleyLNJProof rtc = toDeductionLemmon (parseRipleyLNJ rtc) (purePropFormulaParser ripleyOpts)

ripleyLNJCalc :: NaturalDeductionCalc RipleyLNJ PurePropLexicon (Form Bool)
ripleyLNJCalc = mkNDCalc
    { ndRenderer = LemmonStyle StandardLemmon
    , ndParseProof = parseRipleyLNJProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    }

