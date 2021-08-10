{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Lemmon
    ( parseLemmonProp, LemmonProp(..),  lemmonPropCalc) where

import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes (lhs)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

data LemmonProp =  AndI | AndE1 | AndE2
                | MP    | MT
                | DNI   | DNE
                | BCI   | BCE
                | ORI1  | ORI2 | ORE
                | As    | CP   | RAA1 | RAA2
                deriving (Eq)

instance Show LemmonProp where
        show AndI = "&I"
        show AndE1 = "&E"
        show AndE2 = "&E"
        show MP = "MPP"
        show MT = "MTT"
        show DNI = "DN"
        show DNE = "DN"
        show BCI = "Df.↔"
        show BCE = "Df.↔"
        show ORI1 = "∨I"
        show ORI2 = "∨I"
        show ORE = "∨E"
        show As  = "A"
        show CP = "CP"
        show RAA1  = "RAA"
        show RAA2  = "RAA"

instance Inference LemmonProp PurePropLexicon (Form Bool) where
        ruleOf AndI = adjunction
        ruleOf AndE1 = simplificationVariations !! 0
        ruleOf AndE2 = simplificationVariations !! 1
        ruleOf MP = modusPonens
        ruleOf MT = modusTollens
        ruleOf DNI = doubleNegationIntroduction
        ruleOf DNE = doubleNegationElimination
        ruleOf BCI = biconditionalExchange !! 0
        ruleOf BCE = biconditionalExchange !! 1
        ruleOf ORI1 = additionVariations !! 0
        ruleOf ORI2 = additionVariations !! 1
        ruleOf ORE = explicitSeparationOfCases 2
        ruleOf As = axiom
        ruleOf CP = explicitConditionalProofVariations !! 0
        ruleOf RAA1  = explictConstructiveConjunctionReductioVariations !! 0
        ruleOf RAA2 = explictConstructiveConjunctionReductioVariations !! 2

        globalRestriction (Left ded) n CP = Just (dischargeConstraint n ded (view lhs $ conclusionOf CP))
        globalRestriction (Left ded) n RAA1 = Just (dischargeConstraint n ded (view lhs $ conclusionOf RAA1))
        globalRestriction (Left ded) n RAA2 = Just (dischargeConstraint n ded (view lhs $ conclusionOf RAA2))
        globalRestriction (Left ded) n ORE = Just (dischargeConstraint n ded (view lhs $ conclusionOf ORE))
        globalRestriction _ _ _ = Nothing

        indirectInference CP = Just $ TypedProof (ProofType 1 1)
        indirectInference RAA1 = Just $ TypedProof (ProofType 1 1)
        indirectInference RAA2 = Just $ TypedProof (ProofType 1 1)
        indirectInference ORE = Just $ PolyTypedProof 2 (ProofType 1 1)
        indirectInference _ = Nothing

        isAssumption As = True
        isAssumption _ = False

parseLemmonProp _ n _ = do r <- choice (map (try . string) [ "&I", "&E", "MPP", "MTT", "DN", "Df.↔", "Df.<->"
                                                           , "∨I", "vI", "\\/I", "∨E", "vE", "\\/E", "A", "CP", "RAA", "Pr"])
                           return $ case r of 
                                  r | r == "A" -> [As]
                                    | r == "&I" -> [AndI]
                                    | r == "&E" -> [AndE1, AndE2]
                                    | r == "MP" -> [MP]
                                    | r == "MTT" -> [MT]
                                    | r `elem` ["DN"] -> [DNI, DNE]
                                    | r `elem` ["Df.↔","Df.<->"] -> [BCI, BCE]
                                    | r `elem` ["∨I", "vI", "\\/I"] -> [ORI1, ORI2]
                                    | r `elem` ["∨E", "vE", "\\/E"] -> [ORE]
                                    | r == "RAA" -> [RAA1, RAA2]
                                    | r == "CP" -> [CP]

parseLemmonPropProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) 
            -> String -> [DeductionLine LemmonProp PurePropLexicon (Form Bool)]
parseLemmonPropProof rtc = toDeductionLemmon (parseLemmonProp rtc) (purePropFormulaParser extendedLetters)

lemmonPropNotation :: String -> String
lemmonPropNotation = dropOuterParens . map replace
    where replace '∧' = '&'
          replace '¬' = '-'
          replace c = c

lemmonPropCalc = mkNDCalc
    { ndRenderer = LemmonStyle StandardLemmon
    , ndParseProof = parseLemmonPropProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndNotation = lemmonPropNotation
    }
