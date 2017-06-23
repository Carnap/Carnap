{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.KalishAndMontegue
    (parsePropLogic,  parsePropProof,   PropLogic, propCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

--A system for propositional logic resembling the proof system from Kalish
--and Montegue's LOGIC, with derived rules

data PropLogic = MP | MT  | DNE | DNI | DD   | AX 
                    | CP1 | CP2 | ID1 | ID2  | ID3  | ID4 
                    | ADJ | S1  | S2  | ADD1 | ADD2 | MTP1 | MTP2 | BC1 | BC2 | CB  
                    | DER DerivedRule
               deriving (Eq)

instance Show PropLogic where
        show MP      = "MP"
        show MT      = "MT"
        show DNE     = "DNE"
        show DNI     = "DNI"
        show DD      = "DD"
        show AX      = "PR"
        show CP1     = "CD"
        show CP2     = "CD"
        show ID1     = "ID"
        show ID2     = "ID"
        show ID3     = "ID"
        show ID4     = "ID"
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
        show (DER _) = "Derived"

instance Inference PropLogic PurePropLexicon where
    ruleOf MP        = modusPonens
    ruleOf MT        = modusTollens
    ruleOf AX        = axiom
    ruleOf ID1       = constructiveReductioVariations !! 0
    ruleOf ID2       = constructiveReductioVariations !! 1
    ruleOf ID3       = constructiveReductioVariations !! 2
    ruleOf ID4       = constructiveReductioVariations !! 3
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

    premisesOf (DER r) = zipWith gammafy (premises r) [1..]
        where gammafy p n = GammaV n :|-: SS (liftToSequent p)
    premisesOf r = upperSequents (ruleOf r)

    conclusionOf (DER r) = gammas :|-: SS (liftToSequent $ conclusion r)
        where gammas = foldl (:+:) Top (map GammaV [1..length (premises r)])
    conclusionOf r = lowerSequent (ruleOf r)

    indirectInference x
        | x `elem` [DD,CP1,CP2,ID1,ID2,ID3,ID4] = Just PolyProof
        | otherwise = Nothing

parsePropLogic :: Map String DerivedRule -> Parsec String u [PropLogic]
parsePropLogic ders = do r <- choice (map (try . string) ["AS","PR","MP","MTP","MT","DD","DNE","DNI", "DN", "S", "ADJ",  "ADD" , "BC", "CB",  "CD", "ID", "D-"])
                         case r of
                             "AS"   -> return [AX]
                             "PR"   -> return [AX]
                             "MP"   -> return [MP]
                             "MT"   -> return [MT]
                             "DD"   -> return [DD]
                             "DNE"  -> return [DNE]
                             "DNI"  -> return [DNI]
                             "DN"   -> return [DNE,DNI]
                             "CD"   -> return [CP1,CP2]
                             "ID"   -> return [ID1,ID2,ID3,ID4]
                             "ADJ"  -> return [ADJ]
                             "S"    -> return [S1, S2]
                             "ADD"  -> return [ADD1, ADD2]
                             "MTP"  -> return [MTP1, MTP2]
                             "BC"   -> return [BC1, BC2]
                             "CB"   -> return [CB]
                             "D-" -> do rn <- many1 upper
                                        case M.lookup rn ders of
                                            Just r  -> return [DER r]
                                            Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

parsePropProof :: Map String DerivedRule -> String -> [DeductionLine PropLogic PurePropLexicon (Form Bool)]
parsePropProof ders = toDeduction (parsePropLogic ders) (purePropFormulaParser standardLetters)

propCalc = NaturalDeductionCalc 
    { ndRenderer = MontegueStyle
    , ndParseProof = parsePropProof
    , ndProcessLine = processLine
    , ndProcessLineMemo = Nothing
    , ndParseSeq = propSeqParser
    }
