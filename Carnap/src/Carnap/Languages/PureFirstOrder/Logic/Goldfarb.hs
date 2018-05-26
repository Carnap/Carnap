{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Goldfarb where

import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Core.Data.AbstractSyntaxClasses (lhs)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax (PureLexiconFOL,fogamma)
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic.Rules as P
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser (toDeductionLemmon)
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineLemmonMemo, hoProcessLineLemmon)
import Carnap.Languages.PureFirstOrder.Logic.Rules

data GoldfarbND = TF Int | P | D | UI | UG | CQ1 | CQ2
                  deriving Eq

instance Show GoldfarbND where
        show (TF _)   = "TF"
        show UG       = "UG"
        show P        = "P"
        show D        = "D"
        show UI       = "UI"
        show CQ1      = "CQ"
        show CQ2      = "CQ"

instance Inference GoldfarbND PureLexiconFOL (Form Bool) where

    ruleOf UI = universalInstantiation
    ruleOf UG = universalGeneralization
    ruleOf P = P.axiom
    ruleOf D = P.conditionalProofVariations !! 0
    ruleOf CQ1 = quantifierNegation !! 0
    ruleOf CQ2 = quantifierNegation !! 3
    ruleOf (TF n) = P.explosion n

    restriction (TF n) = Just $ tautologicalConstraint 
                                  (map (\m -> phin m :: FOLSequentCalc (Form Bool)) [1 .. n])
                                  (phin (n + 1) :: FOLSequentCalc (Form Bool))
    restriction UG = Just (eigenConstraint (SeqT 1) (SS (lall "v" $ phi' 1)) (fogamma 1))
    restriction _ = Nothing

    globalRestriction (Left ded) n D = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf D))
    globalRestriction _ _ _ = Nothing

    isAssumption P = True
    isAssumption _ = False

parseGoldfarbND rtc n = do r <- choice (map (try . string) ["P","D","CQ","UI","TF","UG"])
                           case r of 
                              r | r == "P" -> return [P]
                                | r == "D" -> return [D]
                                | r == "CQ" -> return [CQ1,CQ2]
                                | r == "UI" -> return [UI]
                                | r == "UG" -> return [UG]
                                | r == "TF" -> return [TF n]

parseGoldfarbNDProof ::  RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbND PureLexiconFOL (Form Bool)]
parseGoldfarbNDProof ders = toDeductionLemmon (parseGoldfarbND ders) (hardegreePLFormulaParser)

goldfarbNDCalc = NaturalDeductionCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseGoldfarbNDProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseSeq = folSeqParser
    }
