{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Bonevac where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PurePropositional.Logic.Bonevac (BonevacSL(..))
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineHardegreeMemo, hoProcessLineHardegree, processLineHardegree)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules

data BonevacQL = SL BonevacSL | EI | EE | AE | UP
               | QN1 | QN2 | QN3 | QN4 | II | IE | VR
    deriving Eq

instance Show BonevacQL where
    show (SL x) = show x
    show EI = "∃I"
    show EE = "∃E"
    show AE = "∀E"
    show UP = ""
    show QN1 = "QN" 
    show QN2 = "QN"
    show QN3 = "QN"
    show QN4 = "QN"
    show II = "=I"
    show IE = "=E"
    show VR = "VR"

instance Inference BonevacQL PureLexiconFOL (Form Bool) where

    ruleOf EI = existentialGeneralization
    ruleOf EE = existentialInstantiation
    ruleOf AE = universalInstantiation
    ruleOf UP = universalGeneralization
    ruleOf QN1 = quantifierNegation !! 0 
    ruleOf QN2 = quantifierNegation !! 1
    ruleOf QN3 = quantifierNegation !! 2
    ruleOf QN4 = quantifierNegation !! 3
    ruleOf II = eqReflexivity
    ruleOf IE = leibnizLawVariations !! 0
    ruleOf VR = identityRule
    ruleOf r@(SL _) = premisesOf r ∴ conclusionOf r

    premisesOf (SL x) = map liftSequent (premisesOf x)
    premisesOf r = upperSequents (ruleOf r)
    
    conclusionOf (SL x) = liftSequent (conclusionOf x)
    conclusionOf r = lowerSequent (ruleOf r)

    indirectInference (SL x) = indirectInference x
    indirectInference UP = Just (TypedProof (ProofType 0 1)) 
    indirectInference _ = Nothing

    globalRestriction (Left ded) n EE = Just (globalNewConstraint [tau] (Left ded) n )
    globalRestriction (Left ded) n UP = Just (globalNewConstraint [tau] (Left ded) n )
    globalRestriction (Left ded) n (SL As) = Just $ \_ -> if all (== Just [SL As]) . map ruleOfLine . take n $ ded 
                                                             then Nothing
                                                             else Just "assumptions can occur only at the top of the proof"
    globalRestriction _ _ _ = Nothing

    isAssumption (SL x) = isAssumption x
    isAssumption _ = False

parseBonevacQL :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [BonevacQL]
parseBonevacQL rtc = do ms <- optionMaybe (spaces >> eof)
                        case ms of
                            Just _ -> return (map SL [DP, ID1,ID2,ID3,ID4,ID5,ID6,ID7,ID8,IfI1,IfI2] ++ [UP])
                            Nothing -> try parseQL <|> parseSL
    where parseSL = map SL <$> parseBonevacSL (defaultRuntimeDeductionConfig)
          parseQL = do r <- choice (map (try . string) ["∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E","PR"])
                       return $ case r of 
                            r | r `elem` ["∀E","AE"] -> [AE]
                              | r `elem` ["∃I","EI"] -> [EI]
                              | r `elem` ["∃E","EE"] -> [EE]
                              | r == "=I" -> [II]
                              | r == "=E" -> [IE]
                              | r == "QN" -> [QN1,QN2,QN3,QN4]

bonevacQLNotation :: String -> String
bonevacQLNotation (x:xs) = if x `elem` ['A' .. 'Z'] then x : trimParens 0 xs else x : bonevacQLNotation xs
    where trimParens 0 ('(':xs) = trimParens 1 xs
          trimParens 0 xs = bonevacQLNotation xs
          trimParens 1 (')':xs) = bonevacQLNotation xs
          trimParens 1 (',':xs) = trimParens 1 xs
          trimParens n ('(':xs) = '(' : trimParens (n + 1) xs
          trimParens n (')':xs) = ')' : trimParens (n - 1) xs
          trimParens n (x:xs) | x `elem` ['A' .. 'Z'] = x : trimParens n (trimParens 0 xs)
          trimParens n (x:xs) = x : trimParens n xs
          trimParens n [] = []
bonevacQLNotation x = x

parseBonevacQLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine BonevacQL PureLexiconFOL (Form Bool)]
parseBonevacQLProof rtc = toDeductionHardegree (parseBonevacQL rtc) magnusFOLFormulaParser

bonevacQLCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseBonevacQLProof
    , ndProcessLine = processLineHardegree
    , ndProcessLineMemo = Just hoProcessLineHardegreeMemo
    , ndParseSeq = parseSeqOver magnusFOLFormulaParser
    , ndParseForm = magnusFOLFormulaParser
    , ndNotation = bonevacQLNotation
    }
