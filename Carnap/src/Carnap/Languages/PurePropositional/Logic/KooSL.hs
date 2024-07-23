{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.KooSL
    (parseKooSLProof, kooSLCalc, kooSLNotation, KooSL, parseKooSL) where

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
--and Montague's LOGIC, with derived rules, adding Prof. Alex Koo's requested edits.

data KooSL = PR (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               | MP  | MT  | DNE | DNI  | DD   | AS   
               | CP1 | CP2 | ID1 | ID2  | ID3  | ID4  | ID5  | ID6 | ID7 | ID8
               | ADJ | S1  | S2  | ADD1 | ADD2 | MTP1 | MTP2 | BC1 | BC2 | CB | R
               | CDJ1 | CDJ2 | CDJ3 | CDJ4 | TR1 | TR2 | NC1 | NC2 | NB1 | NB2 | NB3 | NB4
               | DM1 | DM2 | DM3 | DM4 | DM5 | DM6 | DM7 | DM8 | MC1 | MC2 | SC1 | SC2 | SC3
               | DER (ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))
               deriving (Eq)

instance Show KooSL where
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
    show R       = "R"
    show (PR _)  = "PR"
    show (DER _) = "Derived"
    show CDJ1    = "CDJ"
    show CDJ2    = "CDJ"
    show CDJ3    = "CDJ"
    show CDJ4    = "CDJ"
    show TR1     = "TR"
    show TR2     = "TR"
    show NC1     = "NC"
    show NC2     = "NC"
    show NB1     = "NB"
    show NB2     = "NB"
    show NB3     = "NB"
    show NB4     = "NB"
    show DM1     = "DM"
    show DM2     = "DM"
    show DM3     = "DM"
    show DM4     = "DM"
    show DM5     = "DM"
    show DM6     = "DM"
    show DM7     = "DM"
    show DM8     = "DM"
    show MC1     = "MC"
    show MC2     = "MC"
    show SC1     = "SC"
    show SC2     = "SC"
    show SC3     = "SC"

instance Inference KooSL PurePropLexicon (Form Bool) where
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
    ruleOf R         = identityRule
    ruleOf CDJ1      = conditionalDisjuctionVariations !! 0
    ruleOf CDJ2      = conditionalDisjuctionVariations !! 1
    ruleOf CDJ3      = conditionalDisjuctionVariations !! 2
    ruleOf CDJ4      = conditionalDisjuctionVariations !! 3
    ruleOf TR1       = transpositionVariations !! 0
    ruleOf TR2       = transpositionVariations !! 1
    ruleOf NC1       = negatedConditionalVariations !! 0
    ruleOf NC2       = negatedConditionalVariations !! 1
    ruleOf NB1       = negatedBiconditionalVariations !! 0
    ruleOf NB2       = negatedBiconditionalVariations !! 1
    ruleOf NB3       = negatedBiconditionalVariations !! 2
    ruleOf NB4       = negatedBiconditionalVariations !! 3
    ruleOf DM1       = deMorgansVariations !! 0
    ruleOf DM2       = deMorgansVariations !! 1
    ruleOf DM3       = deMorgansVariations !! 2
    ruleOf DM4       = deMorgansVariations !! 3
    ruleOf DM5       = deMorgansVariations !! 4
    ruleOf DM6       = deMorgansVariations !! 5
    ruleOf DM7       = deMorgansVariations !! 6
    ruleOf DM8       = deMorgansVariations !! 7
    ruleOf MC1       = materialConditionalVariations !! 0
    ruleOf MC2       = materialConditionalVariations !! 1
    ruleOf SC1       = proofByCases
    ruleOf SC2       = dilemma
    ruleOf SC3       = undecidedDilemma

    premisesOf (DER r) = multiCutLeft r
    premisesOf r = upperSequents (ruleOf r)

    conclusionOf (DER r) = multiCutRight r
    conclusionOf r = lowerSequent (ruleOf r)

    restriction (PR prems) = Just (premConstraint prems)
    restriction _ = Nothing

    indirectInference x
        | x `elem` [DD,CP1,CP2,ID1,ID2,ID3,ID4] = Just PolyProof
        | otherwise = Nothing

parseKooSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [KooSL]
parseKooSL rtc = do r <- choice (map (try . string) ["AS","PR","MP","MTP","MT","DD","DNE","DNI", "DN", "SC", "S", "ADJ",  "ADD" , "BC", "CB", "CDJ", "CD", "ID", "R", "TR", "NC", "NB", "DM", "MC", "D-"])
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
                        "R"    -> return [R]
                        "CDJ"  -> return [CDJ1,CDJ2,CDJ3,CDJ4]
                        "TR"   -> return [TR1, TR2]
                        "NC"   -> return [NC1, NC2]
                        "NB"   -> return [NB1, NB2, NB3, NB4]
                        "DM"   -> return [DM1, DM2, DM3, DM4, DM5, DM6, DM7, DM8]
                        "MC"   -> return [MC1, MC2]
                        "SC"   -> return [SC1, SC2, SC3]
                        "D-" -> do  rn <- many1 upper
                                    case M.lookup rn (derivedRules rtc) of
                                        Just r  -> return [DER r]
                                        Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

parseKooSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) 
                     -> String -> [DeductionLine KooSL PurePropLexicon (Form Bool)]
parseKooSLProof rtc = toDeductionMontague (parseKooSL rtc) (kooSLFormulaParser kooOpts)

kooSLNotation :: String -> String
kooSLNotation = map replace
    where
        replace '⊢' = '∴'
        replace '¬' = '~'
        replace '@' = '∀'
        replace '3' = '∃'
        replace c = c

kooSLCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseKooSLProof
    , ndProcessLine = processLineMontague
    , ndProcessLineMemo = Nothing
    , ndNotation = kooSLNotation
    , ndParseForm = (kooSLFormulaParser kooOpts)
    , ndParseSeq = parseSeqOver (kooSLFormulaParser kooOpts)
    } 
