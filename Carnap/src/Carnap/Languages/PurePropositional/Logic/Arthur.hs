{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Arthur
    ( parseArthurSL, ArthurSL(..), arthurSLCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
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
import Carnap.Languages.Util.LanguageClasses

{-| A system for propositional logic resembling the Statement Logic proof system 
from Arthur's Introduction to Logic book
-}

data ArthurSL = MP | MT 
              | Simp1 | Simp2 | Conj1 | Conj2
              | CS1   | CS2   | Disj1 | Disj2
              | DS1   | DS2   | HS
              | DL    | R
              | CP1   | CP2
              | RA1   | RA2
              | DN1   | DN2
              | DM1   | DM2 | DM3 | DM4
              | BE1   | BE2 
              | TR1   | TR2
              | MI1   | MI2
              | Sup
              | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
              deriving (Eq)
              --skipping derived rules for now

instance Show ArthurSL where
        show MP     = "MP"
        show MT     = "MT"
        show Simp1  = "Simp"
        show Simp2  = "Simp"
        show Conj1  = "Conj"
        show Conj2  = "Conj"
        show CS1    = "CS"
        show CS2    = "CS"
        show Disj1  = "Disj"
        show Disj2  = "Disj"
        show DS1    = "DS"
        show DS2    = "DS"
        show HS     = "HS"
        show DL     = "DL"
        show R      = "R"
        show CP1    = "CP"
        show CP2    = "CP"
        show RA1    = "RA"
        show RA2    = "RA"
        show DN1    = "DN"
        show DN2    = "DN"
        show DM1    = "DM"
        show DM2    = "DM"
        show DM3    = "DM"
        show DM4    = "DM"
        show BE1    = "BE"
        show BE2    = "BE"
        show TR1    = "TR"
        show TR2    = "TR"
        show MI1    = "MI"
        show MI2    = "MI"
        show Sup    = "Supp"
        show (Pr _) = "P"

instance Inference ArthurSL PurePropLexicon (Form Bool) where
        ruleOf MP     = modusPonens
        ruleOf MT     = modusTollens
        ruleOf Simp1  = simplificationVariations !! 0
        ruleOf Simp2  = simplificationVariations !! 1
        ruleOf Conj1  = adjunction
        ruleOf Conj2  = falsumIntroduction
        ruleOf CS1    = conjunctiveSyllogismVariations !! 0
        ruleOf CS2    = conjunctiveSyllogismVariations !! 1
        ruleOf Disj1  = additionVariations !! 0
        ruleOf Disj2  = additionVariations !! 1
        ruleOf DS1    = modusTollendoPonensVariations !! 0 
        ruleOf DS2    = modusTollendoPonensVariations !! 1 
        ruleOf HS     = hypotheticalSyllogism
        ruleOf DL     = dilemma
        ruleOf R      = identityRule
        ruleOf CP1    = conditionalProofVariations !! 0
        ruleOf CP2    = conditionalProofVariations !! 1
        ruleOf RA1    = constructiveFalsumReductioVariations !! 0
        ruleOf RA2    = constructiveFalsumReductioVariations !! 0
        ruleOf DN1    = doubleNegation !! 0
        ruleOf DN2    = doubleNegation !! 1
        ruleOf DM1    = deMorgansLaws !! 0
        ruleOf DM2    = deMorgansLaws !! 1
        ruleOf DM3    = deMorgansLaws !! 2
        ruleOf DM4    = deMorgansLaws !! 3
        ruleOf BE1    = biconditionalExchange !! 0
        ruleOf BE2    = biconditionalExchange !! 1
        ruleOf TR1    = contraposition !! 0
        ruleOf TR2    = contraposition !! 1
        ruleOf MI1    = materialConditional !! 0
        ruleOf MI2    = materialConditional !! 1
        ruleOf Sup = axiom
        ruleOf (Pr _) = axiom

        indirectInference x
            | x `elem` [CP1, CP2, RA1, RA2] = Just PolyProof
            | otherwise = Nothing

        isAssumption Sup = True
        isAssumption _ = False

        isPremise (Pr _) = True
        isPremise _ = False

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n CP1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n CP2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n RA1 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]  
        globalRestriction (Left ded) n RA2 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]  
        globalRestriction _ _ _ = Nothing

parseArthurSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [ArthurSL]
parseArthurSL rtc = do r <- choice (map (try . string) [ "MP", "MT", "Simp", "Conj", "CS", "Disj", "DS", "HS", "DL"
                                                       , "CP", "RA", "DN", "DM", "BE", "TR", "MI", "Supp", "P", "R"])
                       return $ case r of
                        "MP"   -> [MP]
                        "MT"   -> [MT]
                        "Simp" -> [Simp1, Simp2]
                        "Conj" -> [Conj1, Conj2]
                        "CS"   -> [CS1,CS2]
                        "Disj" -> [Disj1, Disj2]
                        "DS"   -> [DS1, DS2]
                        "HS"   -> [HS]
                        "DL"   -> [DL]
                        "R"    -> [R]
                        "CP"   -> [CP1, CP2]
                        "RA"   -> [RA1, RA2]
                        "DN"   -> [DN1, DN2]
                        "DM"   -> [DM1, DM2, DM3, DM4]
                        "BE"   -> [BE1, BE2]
                        "TR"   -> [TR1, TR2]
                        "MI"   -> [MI1, MI2]
                        "Supp" -> [Sup]
                        "P"    -> [Pr (problemPremises rtc)]

parseArthurSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine ArthurSL PurePropLexicon (Form Bool)]
parseArthurSLProof rtc = toDeductionFitch (parseArthurSL rtc) (purePropFormulaParser arthurOpts)

arthurNotation :: String -> String 
arthurNotation = dropOuterParens

arthurSLCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseArthurSLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser arthurOpts)
    , ndParseForm = purePropFormulaParser arthurOpts
    , ndNotation = arthurNotation
    }
