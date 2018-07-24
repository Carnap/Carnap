{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}

module Carnap.Languages.PurePropositional.Logic.Tomassi
    (parseTomassiPL, parseTomassiPLProof, tomassiPLCalc, TomassiPL) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Core.Data.AbstractSyntaxClasses (lhs)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

{-| A system for propositional logic resembling the proof system PL
from Tomassi's Logic book
-}

data TomassiPL =  AndI | AndE1 | AndE2
               | MP    | MT
               | DNI   | DNE
               | BCI   | BCE
               | ORI1  | ORI2 | ORE
               | As    | CP   | RAA   
               | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               deriving (Eq)
              
instance Show TomassiPL where
        show AndI = "&I"
        show AndE1 = "&E"
        show AndE2 = "&E"
        show MP = "MP"
        show MT = "MT"
        show DNI = "~I"
        show DNE = "~E"
        show BCI = "↔I"
        show BCE = "↔E"
        show ORI1 = "∨I"
        show ORI2 = "∨I"
        show ORE = "∨E"
        show As  = "As"
        show CP = "CP"
        show RAA  = "RAA"
        show (Pr _) = "Pr"

instance Inference TomassiPL PurePropLexicon (Form Bool) where
        ruleOf AndI = adjunction
        ruleOf AndE1 = simplificationVariations !! 0
        ruleOf AndE2 = simplificationVariations !! 1
        ruleOf MP = modusPonens
        ruleOf MT = modusTollens
        ruleOf DNI = doubleNegationElimination
        ruleOf DNE = doubleNegationIntroduction
        ruleOf BCI = conditionalToBiconditional
        ruleOf BCE = biconditionalToTwoConditional
        ruleOf ORI1 = additionVariations !! 0
        ruleOf ORI2 = additionVariations !! 1
        ruleOf ORE = explicitSeparationOfCases 2
        ruleOf As = axiom
        ruleOf (Pr _) = axiom
        ruleOf CP = explicitConditionalProofVariations !! 0
        ruleOf RAA = explictConstructiveConjunctionReductioVariations !! 0

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n CP = Just (dischargeConstraint n ded (view lhs $ conclusionOf CP))
        globalRestriction (Left ded) n RAA = Just (dischargeConstraint n ded (view lhs $ conclusionOf RAA))
        globalRestriction (Left ded) n ORE = Just (dischargeConstraint n ded (view lhs $ conclusionOf ORE))
        globalRestriction _ _ _ = Nothing

        indirectInference CP = Just $ TypedProof (ProofType 1 1)
        indirectInference RAA = Just $ TypedProof (ProofType 1 1)
        indirectInference ORE = Just $ PolyTypedProof 2 (ProofType 1 1)
        indirectInference _ = Nothing

        isAssumption As = True
        isAssumption (Pr _) = True
        isAssumption _ = False

parseTomassiPL rtc n _ = do r <- choice (map (try . string) [ "&I", "&E", "MP", "MT", "~I", "~E", "↔I", "<->I", "↔E", "<->E"
                                                            , "∨I", "\\/I", "∨E", "\\/E", "As", "CP", "RAA", "Pr"])
                            return $ case r of 
                                  r | r == "As" -> [As]
                                    | r == "Pr" -> [Pr (problemPremises rtc)] 
                                    | r == "&I" -> [AndI]
                                    | r == "&E" -> [AndE1, AndE2]
                                    | r == "MP" -> [MP]
                                    | r == "MT" -> [MT]
                                    | r == "~I" -> [DNI]
                                    | r == "~E" -> [DNE]
                                    | r `elem` ["↔I","<->I"] -> [BCI]
                                    | r `elem` ["↔E","<->E"] -> [BCE]
                                    | r `elem` ["∨I", "\\/I"] -> [ORI1, ORI2]
                                    | r `elem` ["∨E", "\\/E"] -> [ORE]
                                    | r == "RAA" -> [RAA]
                                    | r == "CP" -> [CP]

parseTomassiPLProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) 
                     -> String -> [DeductionLine TomassiPL PurePropLexicon (Form Bool)]
parseTomassiPLProof rtc = toDeductionLemmonTomassi (parseTomassiPL rtc) (purePropFormulaParser standardLetters)

tomassiPLCalc = NaturalDeductionCalc
    { ndRenderer = LemmonStyle
    , ndParseProof = parseTomassiPLProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseSeq = propSeqParser
    }
