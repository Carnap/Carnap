{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.KalishAndMontague
    (parseMontagueSC,  parseMontagueSCProof, MontagueSC, montagueSCCalc) where

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

--A system for propositional logic resembling the proof system from Kalish
--and Montague's LOGIC, with derived rules

data MontagueSC = PR (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               | MP  | MT  | DNE | DNI  | DD   | AS   
               | CP1 | CP2 | ID1 | ID2  | ID3  | ID4  | ID5  | ID6 | ID7 | ID8
               | ADJ | S1  | S2  | ADD1 | ADD2 | MTP1 | MTP2 | BC1 | BC2 | CB  
               | DER (ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))
               deriving (Eq)

instance Show MontagueSC where
        show MP      = "MP"
        show MT      = "MT"
        show DNE     = "DNE"
        show DNI     = "DNI"
        show DD      = "DD"
        show AS      = "AS"
        show CP1     = "CD"
        show CP2     = "CD"
        show ID1     = "ID"
        show ID2     = "ID"
        show ID3     = "ID"
        show ID4     = "ID"
        show ID5     = "ID"
        show ID6     = "ID"
        show ID7     = "ID"
        show ID8     = "ID"
        show ADJ     = "ADJ"
        show S1      = "S"
        show S2      = "S"
        show ADD1    = "ADD"
        show ADD2    = "ADD"
        show MTP1    = "MTP"
        show MTP2    = "MTP"
        show BC1     = "BC"
        show BC2     = "BC"
        show CB      = "CB"
        show (PR _)  = "PR"
        show (DER _) = "Derived"

instance Inference MontagueSC PurePropLexicon (Form Bool) where
    ruleOf MP        = modusPonens
    ruleOf MT        = modusTollens
    ruleOf AS        = axiom
    ruleOf (PR _)    = axiom
    ruleOf ID1       = constructiveReductioVariations !! 0
    ruleOf ID2       = constructiveReductioVariations !! 1
    ruleOf ID3       = constructiveReductioVariations !! 2
    ruleOf ID4       = constructiveReductioVariations !! 3
    ruleOf ID5       = nonConstructiveReductioVariations !! 0
    ruleOf ID6       = nonConstructiveReductioVariations !! 1
    ruleOf ID7       = nonConstructiveReductioVariations !! 2
    ruleOf ID8       = nonConstructiveReductioVariations !! 3
    ruleOf DD        = identityRule
    ruleOf DNE       = doubleNegationElimination
    ruleOf DNI       = doubleNegationIntroduction
    ruleOf CP1       = conditionalProofVariations !! 0
    ruleOf CP2       = conditionalProofVariations !! 1
    ruleOf ADJ       = adjunction
    ruleOf S1        = simplificationVariations !! 0
    ruleOf S2        = simplificationVariations !! 1
    ruleOf ADD1      = additionVariations !! 0
    ruleOf ADD2      = additionVariations !! 1
    ruleOf MTP1      = modusTollendoPonensVariations !! 0
    ruleOf MTP2      = modusTollendoPonensVariations !! 1
    ruleOf BC1       = biconditionalToConditionalVariations !! 0
    ruleOf BC2       = biconditionalToConditionalVariations !! 1
    ruleOf CB        = conditionalToBiconditional

    premisesOf (DER r) = multiCutLeft r
    premisesOf r = upperSequents (ruleOf r)

    conclusionOf (DER r) = multiCutRight r
    conclusionOf r = lowerSequent (ruleOf r)

    restriction (PR prems) = Just (premConstraint prems)
    restriction _ = Nothing

    indirectInference x
        | x `elem` [DD,CP1,CP2,ID1,ID2,ID3,ID4] = Just PolyProof
        | otherwise = Nothing

parseMontagueSC :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [MontagueSC]
parseMontagueSC rtc = do r <- choice (map (try . string) ["AS","PR","MP","MTP","MT","DD","DNE","DNI", "DN", "S", "ADJ",  "ADD" , "BC", "CB",  "CD", "ID", "D-"])
                         case r of
                             "AS"   -> return [AS]
                             "PR"   -> return [PR (problemPremises rtc)]
                             "MP"   -> return [MP]
                             "MT"   -> return [MT]
                             "DD"   -> return [DD]
                             "DNE"  -> return [DNE]
                             "DNI"  -> return [DNI]
                             "DN"   -> return [DNE,DNI]
                             "CD"   -> return [CP1,CP2]
                             "ID"   -> return [ID1,ID2,ID3,ID4,ID5,ID6,ID7,ID8]
                             "ADJ"  -> return [ADJ]
                             "S"    -> return [S1, S2]
                             "ADD"  -> return [ADD1, ADD2]
                             "MTP"  -> return [MTP1, MTP2]
                             "BC"   -> return [BC1, BC2]
                             "CB"   -> return [CB]
                             "D-" -> do rn <- many1 upper
                                        case M.lookup rn (derivedRules rtc) of
                                            Just r  -> return [DER r]
                                            Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

parseMontagueSCProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) 
                     -> String -> [DeductionLine MontagueSC PurePropLexicon (Form Bool)]
parseMontagueSCProof rtc = toDeductionMontague (parseMontagueSC rtc) (purePropFormulaParser standardLetters)

montagueSCCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseMontagueSCProof
    , ndProcessLine = processLineMontague
    , ndProcessLineMemo = Nothing
    }
