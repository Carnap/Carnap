{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Equivalence () where

import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Equivalence hiding (Pr)

data ZachFOLEq = Prop ZachPropEq | QN1 | QN2 | QN3 | QN4 | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
    deriving (Eq)

instance Show ZachFOLEq where
        show (Prop x) = show x
        show QN1 = "QN"
        show QN2 = "QN"
        show QN3 = "QN"
        show QN4 = "QN"
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
        ruleOf (Pr _) = axiom

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        isPremise (Pr _) = True
        isPremise _ = False

parseZachFOLEq rtc = try quantRule <|> try (map Prop <$> parseProp)
    where parseProp = parseZachPropEq (RuntimeNaturalDeductionConfig mempty mempty)
          quantRule = string "QN" >> return [QN1,QN2,QN3,QN4]

parseZachFOLEqProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine ZachFOLEq PureLexiconFOL (Form Bool)]
parseZachFOLEqProof ders = toDeductionHilbertImplicit (parseZachFOLEq ders) thomasBolducAndZachFOLFormulaParserStrict

zachFOLEqCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseZachFOLEqProof
    , ndProcessLine = hoProcessLineHilbertImplicit
    , ndProcessLineMemo = Just hoProcessLineHilbertImplicitMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOLFormulaParserStrict
    , ndParseForm = thomasBolducAndZachFOLFormulaParserStrict
    }
