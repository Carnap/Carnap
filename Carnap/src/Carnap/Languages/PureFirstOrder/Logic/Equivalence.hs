{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Equivalence (zachFOLEqCalc) where

import Text.Parsec
import Data.Char (toUpper,toLower)
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint, identityRule)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Equivalence hiding (Pr)

data ZachFOLEq = Prop ZachPropEq 
               | QN1  | QN2  | QN3  | QN4 
               | QD1  | QD2  | QD3  | QD4 
               | QSA1 | QSA2 | QSA3 | QSA4
               | QSA5 | QSA6 | QSA7 | QSA8
               | QSA9 | QSA10 | QSA11 |QSA12
               | QSE1 | QSE2 | QSE3 | QSE4
               | QSE5 | QSE6 | QSE7 | QSE8
               | QSE9 | QSE10 | QSE11 |QSE12
               | QXE  | QXA
               | VR   | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
    deriving (Eq)

instance Show ZachFOLEq where
        show (Prop x) = show x
        show QN1 = "QN"
        show QN2 = "QN"
        show QN3 = "QN"
        show QN4 = "QN"
        show QD1 = "QD" 
        show QD2 = "QD"
        show QD3 = "QD"
        show QD4 = "QD"
        show QSA1 = "QSA" 
        show QSA2 = "QSA"
        show QSA3 = "QSA"
        show QSA4 = "QSA"
        show QSA5 = "QSA"
        show QSA6 = "QSA"
        show QSA7 = "QSA"
        show QSA8 = "QSA"
        show QSA9 = "QSA"
        show QSA10 = "QSA"
        show QSA11 = "QSA"
        show QSA12 = "QSA"
        show QSE1 = "QSE" 
        show QSE2 = "QSE"
        show QSE3 = "QSE"
        show QSE4 = "QSE"
        show QSE5 = "QSE"
        show QSE6 = "QSE"
        show QSE7 = "QSE"
        show QSE8 = "QSE"
        show QSE9 = "QSE"
        show QSE10 = "QSE"
        show QSE11 = "QSE"
        show QSE12 = "QSE"
        show QXE   = "QX"
        show QXA   = "QX"
        show VR    = "VR"
        show (Pr _) = "Pr"

instance Inference ZachFOLEq PureLexiconFOL (Form Bool) where
        ruleOf (Prop AndComm) = andCommutativity !! 0
        ruleOf (Prop CommAnd) = andCommutativity !! 1
        ruleOf (Prop OrComm) = orCommutativity !! 0
        ruleOf (Prop CommOr) = orCommutativity !! 1
        ruleOf (Prop IffComm) = iffCommutativity !! 0 
        ruleOf (Prop CommIff) = iffCommutativity !! 1
        ruleOf (Prop DNRep) = doubleNegation !! 0
        ruleOf (Prop RepDN) = doubleNegation !! 1
        ruleOf (Prop MCRep) = materialConditional !! 0
        ruleOf (Prop RepMC) = materialConditional !! 1
        ruleOf (Prop MCRep2) = materialConditional !! 2
        ruleOf (Prop RepMC2) = materialConditional !! 3
        ruleOf (Prop BiExRep) = biconditionalExchange !! 0
        ruleOf (Prop AndAssoc) = andAssociativity !! 0
        ruleOf (Prop AssocAnd) = andAssociativity !! 1
        ruleOf (Prop OrAssoc) = orAssociativity !! 0 
        ruleOf (Prop AssocOr) = orAssociativity !! 1
        ruleOf (Prop AndIdem) = andIdempotence !! 0
        ruleOf (Prop IdemAnd) = andIdempotence !! 1
        ruleOf (Prop OrIdem) = orIdempotence !! 0
        ruleOf (Prop IdemOr) = orIdempotence !! 1
        ruleOf (Prop OrDistL) = orDistributivity !! 0
        ruleOf (Prop DistOrL) = orDistributivity !! 1
        ruleOf (Prop OrDistR) = orDistributivity !! 2
        ruleOf (Prop DistOrR) = orDistributivity !! 3
        ruleOf (Prop AndDistL) = andDistributivity !! 0
        ruleOf (Prop DistAndL) = andDistributivity !! 1
        ruleOf (Prop AndDistR) = andDistributivity !! 2
        ruleOf (Prop DistAndR) = andDistributivity !! 3
        ruleOf (Prop AndAbsorb1) = andAbsorption !! 0
        ruleOf (Prop AbsorbAnd1) = andAbsorption !! 1
        ruleOf (Prop AndAbsorb2) = andAbsorption !! 2
        ruleOf (Prop AbsorbAnd2) = andAbsorption !! 3
        ruleOf (Prop AndAbsorb3) = andAbsorption !! 4
        ruleOf (Prop AbsorbAnd3) = andAbsorption !! 5
        ruleOf (Prop AndAbsorb4) = andAbsorption !! 6
        ruleOf (Prop AbsorbAnd4) = andAbsorption !! 7
        ruleOf (Prop OrAbsorb1) = orAbsorption !! 0
        ruleOf (Prop AbsorbOr1) = orAbsorption !! 1
        ruleOf (Prop OrAbsorb2) = orAbsorption !! 2
        ruleOf (Prop AbsorbOr2) = orAbsorption !! 3
        ruleOf (Prop OrAbsorb3) = orAbsorption !! 4
        ruleOf (Prop AbsorbOr3) = orAbsorption !! 5
        ruleOf (Prop OrAbsorb4) = orAbsorption !! 6
        ruleOf (Prop AbsorbOr4) = orAbsorption !! 7
        ruleOf (Prop NCRep) = negatedConditional !! 0
        ruleOf (Prop RepNC) = negatedConditional !! 1
        ruleOf (Prop RepBiEx) = biconditionalExchange !! 1
        ruleOf (Prop DM1) = deMorgansLaws !! 0
        ruleOf (Prop DM2) = deMorgansLaws !! 1
        ruleOf (Prop DM3) = deMorgansLaws !! 2
        ruleOf (Prop DM4) = deMorgansLaws !! 3
        ruleOf (Prop Simp1) = andTautCancellation !! 0
        ruleOf (Prop Simp2) = andTautCancellation !! 1 
        ruleOf (Prop Simp3) = andTautCancellation !! 2 
        ruleOf (Prop Simp4) = andTautCancellation !! 3 
        ruleOf (Prop Simp5) = andTautCancellation !! 4 
        ruleOf (Prop Simp6) = andTautCancellation !! 5 
        ruleOf (Prop Simp7) = andTautCancellation !! 6 
        ruleOf (Prop Simp8) = andTautCancellation !! 7 
        ruleOf (Prop Simp9) = orTautCancellation !! 0
        ruleOf (Prop Simp10) = orTautCancellation !! 1
        ruleOf (Prop Simp11) = orTautCancellation !! 2
        ruleOf (Prop Simp12) = orTautCancellation !! 3
        ruleOf (Prop Simp13) = orTautCancellation !! 4
        ruleOf (Prop Simp14) = orTautCancellation !! 5
        ruleOf (Prop Simp15) = orTautCancellation !! 6
        ruleOf (Prop Simp16) = orTautCancellation !! 7
        ruleOf (Prop Simp17) = andContCancellation !! 0
        ruleOf (Prop Simp18) = andContCancellation !! 1
        ruleOf (Prop Simp19) = andContCancellation !! 2
        ruleOf (Prop Simp20) = andContCancellation !! 3
        ruleOf (Prop Simp21) = andContCancellation !! 4
        ruleOf (Prop Simp22) = andContCancellation !! 5
        ruleOf (Prop Simp23) = andContCancellation !! 6
        ruleOf (Prop Simp24) = andContCancellation !! 7
        ruleOf (Prop Simp25) = orContCancellation !! 0
        ruleOf (Prop Simp26) = orContCancellation !! 1
        ruleOf (Prop Simp27) = orContCancellation !! 2
        ruleOf (Prop Simp28) = orContCancellation !! 3
        ruleOf (Prop Simp29) = orContCancellation !! 4
        ruleOf (Prop Simp30) = orContCancellation !! 5
        ruleOf (Prop Simp31) = orContCancellation !! 6
        ruleOf (Prop Simp32) = orContCancellation !! 7
        ruleOf QN1 = quantifierNegationReplace !! 0
        ruleOf QN2 = quantifierNegationReplace !! 1
        ruleOf QN3 = quantifierNegationReplace !! 2
        ruleOf QN4 = quantifierNegationReplace !! 3
        ruleOf QD1 = quantifierDistribution !! 0 
        ruleOf QD2 = quantifierDistribution !! 1
        ruleOf QD3 = quantifierDistribution !! 2 
        ruleOf QD4 = quantifierDistribution !! 3 
        ruleOf QSA1 = rulesOfPassage !! 2
        ruleOf QSA2 = rulesOfPassage !! 3 
        ruleOf QSA3 = rulesOfPassage !! 6 
        ruleOf QSA4 = rulesOfPassage !! 7 
        ruleOf QSA5 = rulesOfPassage !! 10 
        ruleOf QSA6 = rulesOfPassage !! 11 
        ruleOf QSA7 = rulesOfPassage !! 14 
        ruleOf QSA8 = rulesOfPassage !! 15 
        ruleOf QSA9 = conditionalRulesOfPassage !! 0
        ruleOf QSA10 = conditionalRulesOfPassage !! 1
        ruleOf QSA11 = conditionalRulesOfPassage !! 4
        ruleOf QSA12 = conditionalRulesOfPassage !! 5
        ruleOf QSE1 = rulesOfPassage !! 0
        ruleOf QSE2 = rulesOfPassage !! 1 
        ruleOf QSE3 = rulesOfPassage !! 4 
        ruleOf QSE4 = rulesOfPassage !! 5 
        ruleOf QSE5 = rulesOfPassage !! 8
        ruleOf QSE6 = rulesOfPassage !! 9
        ruleOf QSE7 = rulesOfPassage !! 12
        ruleOf QSE8 = rulesOfPassage !! 13 
        ruleOf QSE9 = conditionalRulesOfPassage !! 2
        ruleOf QSE10 = conditionalRulesOfPassage !! 3
        ruleOf QSE11 = conditionalRulesOfPassage !! 6
        ruleOf QSE12 = conditionalRulesOfPassage !! 7
        ruleOf QXE = quantifierExchange !! 0
        ruleOf QXA = quantifierExchange !! 2
        ruleOf VR = identityRule
        ruleOf (Pr _) = axiom

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        isPremise (Pr _) = True
        isPremise _ = False

parseZachFOLEq rtc = try quantRule <|> try (map Prop <$> parseProp)
    where parseProp = parseZachPropEq (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . caseInsensitiveString) ["QN","QD","QSA","QSE","QX","VR","PR"])
                         return $ case map toLower r of 
                            "qn" -> [QN1,QN2,QN3,QN4]
                            "qd" -> [QD1,QD2,QD3,QD4]
                            "qsa" -> [QSA1,QSA2, QSA3, QSA4, QSA5, QSA6, QSA7, QSA8, QSA9, QSA10, QSA11, QSA12]
                            "qse" -> [QSE1,QSE2, QSE3, QSE4, QSE5, QSE6, QSE7, QSE8, QSE9, QSE10, QSE11, QSE12]
                            "qx" -> [QXA, QXE]
                            "vr" -> [VR]
                            "pr" -> [Pr (problemPremises rtc)]
          caseInsensitiveChar c = char (toLower c) <|> char (toUpper c)
          caseInsensitiveString s = try (mapM caseInsensitiveChar s) <?> "\"" ++ s ++ "\""

parseZachFOLEqProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine ZachFOLEq PureLexiconFOL (Form Bool)]
parseZachFOLEqProof ders = toDeductionHilbertImplicit (parseZachFOLEq ders) thomasBolducAndZachFOL2019FormulaParserStrict

zachFOLEqCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseZachFOLEqProof
    , ndProcessLine = hoProcessLineHilbertImplicit
    , ndProcessLineMemo = Just hoProcessLineHilbertImplicitMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOL2019FormulaParserStrict
    , ndParseForm = thomasBolducAndZachFOL2019FormulaParserStrict
    , ndNotation = ndNotation zachPropEqCalc
    }
