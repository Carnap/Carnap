{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Lande
    ( parseLandeProp, LandeProp(..),  landePropCalc) where

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

data LandeProp =  AndI | AndE1 | AndE2
                | MP    | DNE
                | BCI   | BCE
                | ORI1  | ORI2 | ORE
                | As    | CP   | RAA1 | RAA2
                deriving (Eq)

instance Show LandeProp where
        show AndI = "∧I"
        show AndE1 = "∧E"
        show AndE2 = "∧E"
        show MP = "→E"
        show DNE = "--E"
        show BCI = "↔I"
        show BCE = "↔E"
        show ORI1 = "∨I"
        show ORI2 = "∨I"
        show ORE = "∨E"
        show As  = "A"
        show CP = "→I"
        show RAA1  = "-I"
        show RAA2  = "-I"

instance Inference LandeProp PurePropLexicon (Form Bool) where
        ruleOf AndI = adjunction
        ruleOf AndE1 = simplificationVariations !! 0
        ruleOf AndE2 = simplificationVariations !! 1
        ruleOf MP = modusPonens
        ruleOf DNE = doubleNegationElimination
        ruleOf BCE = biconditionalExchange !! 0
        ruleOf BCI = biconditionalExchange !! 1
        ruleOf ORI1 = additionVariations !! 0
        ruleOf ORI2 = additionVariations !! 1
        ruleOf ORE = dilemma
        ruleOf As = axiom
        ruleOf CP = explicitConditionalProofVariations !! 0
        ruleOf RAA1  = explictConstructiveConjunctionReductioVariations !! 0
        ruleOf RAA2 = explictConstructiveConjunctionReductioVariations !! 2

        globalRestriction (Left ded) n CP = Just (dischargeConstraint n ded (view lhs $ conclusionOf CP))
        globalRestriction (Left ded) n RAA1 = Just (dischargeConstraint n ded (view lhs $ conclusionOf RAA1))
        globalRestriction (Left ded) n RAA2 = Just (dischargeConstraint n ded (view lhs $ conclusionOf RAA2))
        globalRestriction _ _ _ = Nothing

        indirectInference CP = Just $ TypedProof (ProofType 1 1)
        indirectInference RAA1 = Just $ TypedProof (ProofType 1 1)
        indirectInference RAA2 = Just $ TypedProof (ProofType 1 1)
        indirectInference _ = Nothing

        isAssumption As = True
        isAssumption _ = False

parseLandeProp _ n _ = do r <- choice (map (try . string) [ "∧I", "^I", "/\\I","∧E", "^E", "/\\E", "→E", "->E"
                                                          , "¬¬E","~~E","--E", "↔I", "<->I", "↔E","<->E" , "∨I"
                                                          , "vI", "\\/I", "∨E", "vE", "\\/E",  "→I", "->I", "¬I"
                                                          , "~I" , "-I", "A"])
                          return $ case r of 
                                  r | r == "A" -> [As]
                                    | r `elem` ["∧I", "^I", "/\\I"] -> [AndI]
                                    | r `elem` ["∧E", "^E", "/\\E"] -> [AndE1, AndE2]
                                    | r `elem` ["→E", "->E"] -> [MP]
                                    | r `elem` ["¬¬E","~~E","--E"] -> [DNE]
                                    | r `elem` ["↔I","<->I"] -> [BCI]
                                    | r `elem` ["↔E","<->E"] -> [BCE]
                                    | r `elem` ["∨I", "vI", "\\/I"] -> [ORI1, ORI2]
                                    | r `elem` ["∨E", "vE", "\\/E"] -> [ORE]
                                    | r `elem` ["¬I", "~I", "-I"] -> [RAA1, RAA2]
                                    | r `elem` ["→I", "->I"] -> [CP]

parseLandePropProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) 
            -> String -> [DeductionLine LandeProp PurePropLexicon (Form Bool)]
parseLandePropProof rtc = toDeductionLemmon (parseLandeProp rtc) (purePropFormulaParser landeOpts)

landePropNotation :: String -> String 
landePropNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> dropOuterParens s
    where altparser = do s <- handleCon <|> handleschema <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handleschema = (char 'φ' >> return "◯")
                  <|> (char 'ψ' >> return "□")
                  <|> (char 'χ' >> return "△")
          handleCon = (char '¬' >> return "-")
                  <|> (char '⊤' >> return " ")
                  <|> (char '∅' >> return " ")
          fallback = do c <- anyChar 
                        return [c]

landePropCalc = mkNDCalc
    { ndRenderer = LemmonStyle StandardLemmon
    , ndParseProof = parseLandePropProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndNotation = landePropNotation
    , ndParseForm = purePropFormulaParser landeOpts
    , ndParseSeq = parseSeqOver (purePropFormulaParser landeOpts)
    }
