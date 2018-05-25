{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Goldfarb where

import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Core.Data.AbstractSyntaxClasses (lhs)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax (PureLexiconFOL)
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic.Rules as P
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser (toDeductionLemmon)
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineLemmonMemo, hoProcessLineLemmon)
import Carnap.Languages.PureFirstOrder.Logic.Rules

data GoldfarbND = TF | P | D | UI | CQ1 | CQ2
                  deriving Eq

instance Show GoldfarbND where
        show TF   = "TF"
        show P    = "P"
        show D    = "D"
        show UI   = "UI"
        show CQ1  = "CQ"
        show CQ2  = "CQ"

instance Inference GoldfarbND PureLexiconFOL (Form Bool) where

    ruleOf UI = universalInstantiation
    ruleOf P = P.axiom
    ruleOf D = P.conditionalProofVariations !! 0
    ruleOf CQ1 = quantifierNegation !! 0
    ruleOf CQ2 = quantifierNegation !! 3
    ruleOf TF = P.explosion

    restriction TF = Just $ tautologicalConstraint 
                                (phin 1 :: FOLSequentCalc (Form Bool))
                                (phin 2 :: FOLSequentCalc (Form Bool))
              
    restriction _ = Nothing

    globalRestriction (Left ded) n D = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf D))
    globalRestriction _ _ _ = Nothing

    isAssumption P = True
    isAssumption _ = False

parseGoldfarbND rtc = do r <- choice (map (try . string) ["P","D","CQ","UI","TF"])
                         case r of 
                            r | r == "P" -> return [P]
                              | r == "D" -> return [D]
                              | r == "CQ" -> return [CQ1,CQ2]
                              | r == "UI" -> return [UI]
                              | r == "TF" -> return [TF]

parseGoldfarbNDProof ::  RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbND PureLexiconFOL (Form Bool)]
parseGoldfarbNDProof ders = toDeductionLemmon (parseGoldfarbND ders) (hardegreePLFormulaParser)

goldfarbNDCalc = NaturalDeductionCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseGoldfarbNDProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseSeq = folSeqParser
    }
