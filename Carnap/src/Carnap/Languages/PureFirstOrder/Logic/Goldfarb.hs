{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Goldfarb where

import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.Types (Form,Term)
import Carnap.Core.Data.Classes (lhs)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PureFirstOrder.Syntax (PureLanguageFOL, PureLexiconFOL,fogamma)
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic.Rules as P
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

data GoldfarbND = TF Int | P   | D   | UI  | UG 
                | CQ1    | CQ2 | CQ3 | CQ4 | CQ5 | CQ6 | CQ7 | CQ8
                  deriving Eq

instance Show GoldfarbND where
        show (TF _)   = "TF"
        show UG       = "UG"
        show P        = "P"
        show D        = "D"
        show UI       = "UI"
        show CQ1      = "CQ"
        show CQ2      = "CQ"
        show CQ3      = "CQ"
        show CQ4      = "CQ"
        show CQ5      = "CQ"
        show CQ6      = "CQ"
        show CQ7      = "CQ"
        show CQ8      = "CQ"

instance Inference GoldfarbND PureLexiconFOL (Form Bool) where

    ruleOf UI = universalInstantiation
    ruleOf UG = universalGeneralization
    ruleOf P = P.axiom
    ruleOf D = P.explicitConditionalProofVariations !! 0
    ruleOf CQ1 = quantifierNegation !! 0
    ruleOf CQ2 = quantifierNegation !! 1
    ruleOf CQ3 = quantifierNegation !! 2
    ruleOf CQ4 = quantifierNegation !! 3
    ruleOf CQ5 = quantifierNegation !! 4
    ruleOf CQ6 = quantifierNegation !! 5
    ruleOf CQ7 = quantifierNegation !! 6
    ruleOf CQ8 = quantifierNegation !! 7
    ruleOf (TF n) = P.explosion n

    restriction (TF n) = Just $ tautologicalConstraint 
                                  (map (\m -> phin m :: FOLSequentCalc (Form Bool)) [1 .. n])
                                  (phin (n + 1) :: FOLSequentCalc (Form Bool))
    restriction UG = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
    restriction _ = Nothing

    globalRestriction (Left ded) n D = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf D))
    globalRestriction _ _ _ = Nothing

    indirectInference D = Just $ TypedProof (ProofType 1 1)
    indirectInference _ = Nothing

    isAssumption P = True
    isAssumption _ = False

parseGoldfarbND rtc n _ = do r <- choice (map (try . string) ["P","D","CQ","UI","TF","UG"])
                             case r of 
                                  r | r == "P" -> return [P]
                                    | r == "D" -> return [D]
                                    | r == "CQ" -> return [CQ1,CQ2,CQ3,CQ4,CQ5,CQ6,CQ7,CQ8]
                                    | r == "UI" -> return [UI]
                                    | r == "UG" -> return [UG]
                                    | r == "TF" -> return [TF n]

parseGoldfarbNDProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbND PureLexiconFOL (Form Bool)]
parseGoldfarbNDProof ders = toDeductionLemmonGoldfarb (parseGoldfarbND ders) goldfarbNDFormulaParser

parseGoldfarbBrownNDProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbND PureLexiconFOL (Form Bool)]
parseGoldfarbBrownNDProof ders = toDeductionLemmonBrown (parseGoldfarbND ders) goldfarbNDFormulaParser

goldfarbNDNotation :: String -> String 
goldfarbNDNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- try handleAtom <|> try handleQuant <|> try handleCon <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          handleQuant = do q <- oneOf "∀∃"
                           v <- anyChar
                           return $ "(" ++ [q] ++ [v] ++ ")"
          handleCon = (char '∧' >> return "∙") <|> (char '¬' >> return "-") 
                                               <|> (char '→' >> return "⊃") 
                                               <|> (char '↔' >> return "≡")
          fallback = do c <- anyChar 
                        return [c]

goldfarbNDCalc = mkNDCalc
    { ndRenderer = LemmonStyle GoldfarbStyle
    , ndParseProof = parseGoldfarbNDProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseForm = goldfarbNDFormulaParser
    , ndParseSeq = parseSeqOver goldfarbNDFormulaParser
    , ndNotation = goldfarbNDNotation 
    }

goldfarbBrownNDCalc = goldfarbNDCalc { ndParseProof = parseGoldfarbBrownNDProof }

------------------------------------------------------------------------
--  2. The system with convenience rules for existential quantifiers  --
------------------------------------------------------------------------

data GoldfarbNDPlus = ND GoldfarbND | EG | EII String | EIE
                        deriving Eq

instance Show GoldfarbNDPlus where
        show (ND s) = show s
        show EG = "EG"
        show (EII v) = "EII(" ++ v ++ ")" 
        show EIE = "EIE"
        --XXX: including v is important, since the memoization relies
        --hashing the rule, which relies on its show instance

instance Inference GoldfarbNDPlus PureLexiconFOL (Form Bool) where

    ruleOf (ND s) = ruleOf s
    ruleOf EG = existentialGeneralization
    ruleOf (EII _) = existentialAssumption
    ruleOf EIE = existentialAssumptionDischarge

    restriction (ND s) = restriction s
    restriction _ = Nothing

    globalRestriction (Left ded) n (ND D) = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf (ND D)))
    globalRestriction (Left ded) n (EII v) = case parse (parseFreeVar ['a'..'z'] :: Parsec String u (PureLanguageFOL (Term Int))) "" v  of
                                                 Left e -> Just (const $ Just "couldn't parse flagged term")
                                                 Right v' -> Just (totallyFreshConstraint n ded (taun 1) v')
    globalRestriction (Left ded) n EIE = Just (P.dischargeConstraint n ded (view lhs $ conclusionOf EIE)
                                              `andFurtherRestriction` flaggedVariableConstraint n ded theSuc checkEII)
        where checkEII (EII v) = case parse (parseFreeVar ['a'..'z'] :: Parsec String u (PureLanguageFOL (Term Int))) "" v of
                                     Right v' -> Right (liftToSequent v')
                                     Left e -> Left "couldn't parse flagged term"
              checkEII _ = Left "The discharged premise is not justified with EII"
              theSuc = SS (phin 1 :: FOLSequentCalc (Form Bool))

    globalRestriction _ _ _ = Nothing

    indirectInference (ND x) = indirectInference x
    indirectInference EIE = Just $ TypedProof (ProofType 1 1)
    indirectInference _ = Nothing

    isAssumption (ND s)  = isAssumption s
    isAssumption (EII _) = True
    isAssumption _ = False

parseGoldfarbNDPlus rtc n annote = plusRules <|> (map ND <$> parseGoldfarbND rtc n annote)
            where plusRules = do r <- choice (map (try . string) ["EG","EII","EIE"])
                                 case r of 
                                        r | r == "EG" -> return [EG]
                                          | r == "EII" -> return [EII annote]
                                          | r == "EIE" -> return [EIE]

parseGoldfarbNDPlusProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbNDPlus PureLexiconFOL (Form Bool)]
parseGoldfarbNDPlusProof rtc = toDeductionLemmonGoldfarb (parseGoldfarbNDPlus rtc) goldfarbNDFormulaParser

parseGoldfarbBrownNDPlusProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GoldfarbNDPlus PureLexiconFOL (Form Bool)]
parseGoldfarbBrownNDPlusProof rtc = toDeductionLemmonBrown (parseGoldfarbNDPlus rtc) goldfarbNDFormulaParser

goldfarbNDPlusCalc = mkNDCalc
    { ndRenderer = LemmonStyle GoldfarbStyle
    , ndParseProof = parseGoldfarbNDPlusProof
    , ndProcessLine = hoProcessLineLemmon
    , ndParseForm = goldfarbNDFormulaParser
    , ndParseSeq = parseSeqOver goldfarbNDFormulaParser
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndNotation = goldfarbNDNotation 
    }

goldfarbBrownNDPlusCalc = goldfarbNDPlusCalc { ndParseProof = parseGoldfarbBrownNDPlusProof }
