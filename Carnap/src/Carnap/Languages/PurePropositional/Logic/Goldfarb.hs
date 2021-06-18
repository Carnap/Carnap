{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Goldfarb where

import Text.Parsec
import Data.Char
import Control.Lens (view)
import Carnap.Core.Data.Types (Form,Term)
import Carnap.Core.Data.Classes (lhs)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser (toDeductionLemmonGoldfarb, toDeductionLemmonBrown)
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineLemmonMemo, hoProcessLineLemmon)
import Carnap.Languages.PureFirstOrder.Logic.Rules

------------------------------------
--  1. The basic Goldfarb system  --
------------------------------------

--this is a natural deduction system for propositional logic, based on
--Goldfarb's, with some additions by James Pearson

data GoldfarbPropND =  P   | D   | MP  | MT 
                    | DNI  | DNE | CI  | CE1 | CE2
                    | DI1  | DI2 | DE1 | DE2 | BI   | BE1 | BE2
                    | RA   | RC  | I1  | I2  | NDE1 | NDE2
        deriving Eq

instance Show GoldfarbPropND where
    show P   = "P" 
    show D   = "D" 
    show MP  = "MP"
    show MT  = "MT"
    show DNI = "DN"  
    show DNE = "DN" 
    show CI  = "CI"
    show CE1 = "CE" 
    show CE2 = "CE"
    show DI1 = "DI"  
    show DI2 = "DI"  
    show DE1 = "DE" 
    show DE2 = "DE" 
    show BI  = "BI"
    show BE1 = "BE" 
    show BE2 = "BE"
    show RA  = "RA"  
    show RC  = "RC" 
    show I1  = "I"
    show I2  = "I"
    show NDE1 = "NDE"
    show NDE2 = "NDE"

instance Inference GoldfarbPropND PurePropLexicon (Form Bool) where

    ruleOf P    = axiom
    ruleOf D    = explicitConditionalProofVariations !! 0
    ruleOf MP   = modusPonens
    ruleOf MT   = modusTollens
    ruleOf DNI  = doubleNegationIntroduction
    ruleOf DNE  = doubleNegationElimination
    ruleOf CI   = adjunction
    ruleOf CE1  = simplificationVariations !! 0
    ruleOf CE2  = simplificationVariations !! 1
    ruleOf DI1  = additionVariations !! 0
    ruleOf DI2  = additionVariations !! 1
    ruleOf DE1  = modusTollendoPonensVariations !! 0 
    ruleOf DE2  = modusTollendoPonensVariations !! 1
    ruleOf BI   = conditionalToBiconditional
    ruleOf BE1  = biconditionalToConditionalVariations !! 0
    ruleOf BE2  = biconditionalToConditionalVariations !! 1
    ruleOf RA   = conditionalReductio
    ruleOf RC   = proofByCases
    ruleOf I1   = biconditionalInterchange !! 0
    ruleOf I2   = biconditionalInterchange !! 1
    ruleOf NDE1 = negatedDisjunctionVariations !! 0
    ruleOf NDE2 = negatedDisjunctionVariations !! 1

    restriction _ = Nothing

    globalRestriction (Left ded) n D = Just (dischargeConstraint n ded (view lhs $ conclusionOf D))
    globalRestriction _ _ _ = Nothing

    indirectInference D = Just $ TypedProof (ProofType 1 1)
    indirectInference _ = Nothing

    isAssumption P = True
    isAssumption _ = False

parseGoldfarbPropND rtc n _ = do r <- choice (map (try . string) [ "NDE", "MP", "MT", "DN",  "CI", "CE", "DI", "DE", "BI", "BE", "RA", "RC", "I", "P", "D"])
                                 return $ case r of 
                                      r | r == "P" -> [P]
                                        | r == "D" -> [D]
                                        | r == "MP" -> [MP]   
                                        | r == "MT" -> [MT]
                                        | r == "DN" -> [DNI, DNE]
                                        | r == "CI" -> [CI]
                                        | r == "CE" -> [CE1, CE2]
                                        | r == "DI" -> [DI1,DI2]
                                        | r == "DE" -> [DE1, DE2]
                                        | r == "BI" -> [BI]
                                        | r == "BE" -> [BE1, BE2]
                                        | r == "RA" -> [RA]
                                        | r == "RC" -> [RC, RC]
                                        | r == "I" -> [I1, I2]
                                        | r == "NDE" -> [NDE1, NDE2]
                                   
parseGoldfarbPropNDProof ::  RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GoldfarbPropND PurePropLexicon (Form Bool)]
parseGoldfarbPropNDProof ders = toDeductionLemmonGoldfarb (parseGoldfarbPropND ders) (purePropFormulaParser gamutOpts)

goldfarbPropNDNotation :: String -> String 
goldfarbPropNDNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleCon <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleCon = (char '∧' >> return "∙") <|> (char '¬' >> return "-") <|> (char '→' >> return "⊃") <|> (char '↔' >> return "≡")
          fallback = do c <- anyChar 
                        return [toLower c]

goldfarbPropNDCalc = mkNDCalc
    { ndRenderer = LemmonStyle GoldfarbStyle
    , ndParseProof = parseGoldfarbPropNDProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = goldfarbPropNDNotation
    }
