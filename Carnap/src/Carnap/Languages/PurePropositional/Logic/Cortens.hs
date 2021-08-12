{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Cortens
    (parseCortensSL,  parseCortensSLProof, CortensSL, cortensSLCalc) where
import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

data CortensSL = PR (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               | AndI  | AndE1 | AndE2
               | IfI1  | IfI2  | IfE
               | NegI1 | NegI2 | NegE
               | OrI1  | OrI2  | OrE1 | OrE2
               | BCI   | BCE1  | BCE2
               | AS
               deriving (Eq)

instance Show CortensSL where
    show (PR _) = "PR"
    show AS = "AS"
    show AndI = "∧I"
    show AndE1 = "∧E" 
    show AndE2 = "∧E"
    show IfI1 = "→I"
    show IfI2 = "→I"
    show IfE = "→E"
    show NegI1 = "¬I"
    show NegI2 = "¬I"
    show NegE = "¬E"
    show OrI1 = "∨I"
    show OrI2 = "∨I"
    show OrE1 = "∨E"
    show OrE2 = "∨E"
    show BCI = "↔I"
    show BCE1 = "↔E"
    show BCE2 = "↔E"

instance Inference CortensSL PurePropLexicon (Form Bool) where
    ruleOf (PR _) = axiom
    ruleOf AS = axiom
    ruleOf AndI = adjunction
    ruleOf AndE1 = simplificationVariations !! 0 
    ruleOf AndE2 = simplificationVariations !! 1 
    ruleOf IfI1 = explicitConditionalProofVariations !! 0
    ruleOf IfI2 = explicitConditionalProofVariations !! 1
    ruleOf IfE = modusPonens
    ruleOf NegI1 = explictConstructiveConjunctionReductioVariations !! 0 
    ruleOf NegI2 = explictConstructiveConjunctionReductioVariations !! 1
    ruleOf NegE = doubleNegationElimination
    ruleOf OrI1 = additionVariations !! 0
    ruleOf OrI2 = additionVariations !! 1
    ruleOf OrE1 = modusTollendoPonensVariations !! 0
    ruleOf OrE2 = modusTollendoPonensVariations !! 1
    ruleOf BCI = conditionalToBiconditional
    ruleOf BCE1 = biconditionalToConditionalVariations !! 0
    ruleOf BCE2 = biconditionalToConditionalVariations !! 1

    premisesOf r = upperSequents (ruleOf r)

    conclusionOf r = lowerSequent (ruleOf r)

    restriction (PR prems) = Just (premConstraint prems)
    restriction _ = Nothing

    isAssumption AS = True
    isAssumption _ = False

    isPremise (PR _) = True
    isPremise _ = False

    indirectInference x
        | x `elem` [NegI1, NegI2, IfI1, IfI2] = Just assumptiveProof
        | otherwise = Nothing

parseCortensSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [CortensSL]
parseCortensSL rtc = do r <- choice (map (try . string) ["AS","PR","/\\I", "^I", "∧I","/\\E","^E", "∧E","->I","→I","->E", "→E"
                                                         ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","<->I", "↔I" 
                                                         , "<->E", "↔E"]) 
                        return $ case r of
                            r | r == "AS" -> [AS]
                              | r == "PR" -> [PR (problemPremises rtc)]
                              | r `elem` ["/\\I","^I", "∧I"] -> [AndI]
                              | r `elem` ["/\\E","^E","∧E"] -> [AndE1, AndE2]
                              | r `elem` ["->I","→I"]  -> [IfI1, IfI2]
                              | r `elem` ["->E", "→E"] -> [IfE]
                              | r `elem` ["~I","¬I","-I"] -> [NegI1, NegI2]
                              | r `elem` ["~E","¬E","-E"] -> [NegE]
                              | r `elem` ["vI","\\/I"] -> [OrI1, OrI2]
                              | r `elem` ["vE","\\/E"] -> [OrE1, OrE2]
                              | r `elem` ["BI","<->I","↔I"] -> [BCI]
                              | r `elem` ["BE","<->E","↔E"] -> [BCE1, BCE2]

parseCortensSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) 
                     -> String -> [DeductionLine CortensSL PurePropLexicon (Form Bool)]
parseCortensSLProof rtc = toDeductionFitchAlt (parseCortensSL rtc) (purePropFormulaParser extendedLetters)

cortensNotation :: String -> String 
cortensNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> s
    where altparser = do s <- handleschema <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handleschema = (char 'φ' >> return "◯")
                  <|> (char 'ψ' >> return "□")
                  <|> (char 'χ' >> return "△")
          fallback = do c <- anyChar 
                        return [c]

cortensSLCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseCortensSLProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Nothing
    , ndNotation = cortensNotation
    }

