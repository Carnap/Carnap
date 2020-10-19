{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Hardegree (hardegreePLCalc,parseHardegreePL) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Languages.PurePropositional.Logic.Hardegree (hardegreeNotation)
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineHardegreeMemo, hoProcessLineHardegree)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules

--------------------
--  1. System PL  --
--------------------
-- A system of first-order logic resembling system PL from Hardegree's
-- Introduction to Modal Logic

data HardegreePL = HardegreeSL P.HardegreeSL | UI | UE | EI | EE 
                 | QN1 | QN2 | QN3 | QN4
                 | NUO | NEO
                 deriving Eq

instance Show HardegreePL where
        show (HardegreeSL x) = show x
        show UI          = "UD"
        show UE          = "∀O"
        show EI          = "∃I"
        show EE          = "∃O"
        show QN1         = "QN"
        show QN2         = "QN"
        show QN3         = "QN"
        show QN4         = "QN"
        show NUO         = "~∀O"
        show NEO         = "~∃O"

instance Inference HardegreePL PureLexiconFOL (Form Bool) where

         ruleOf UI   = universalGeneralization
         ruleOf UE   = universalInstantiation
         ruleOf EI   = existentialGeneralization
         ruleOf EE   = existentialInstantiation
         ruleOf QN1  = quantifierNegation !! 0
         ruleOf QN2  = quantifierNegation !! 1
         ruleOf QN3  = quantifierNegation !! 2
         ruleOf QN4  = quantifierNegation !! 3
         ruleOf NUO  = negatedUniversalInstantiation
         ruleOf NEO  = negatedExistentialInstantiation

         premisesOf (HardegreeSL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (HardegreeSL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (HardegreeSL x) = indirectInference x
         indirectInference UI = Just (TypedProof (ProofType 0 1)) 
         indirectInference _ = Nothing

         globalRestriction (Left ded) n UE = Just (globalOldConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n EE = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n NEO = Just (globalOldConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n NUO = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction _ _ _ = Nothing

         isAssumption (HardegreeSL x) = isAssumption x
         isAssumption _ = False

parseHardegreePL rtc = try liftProp <|> quantRule
    where liftProp = do r <- P.parseHardegreeSL (RuntimeNaturalDeductionConfig mempty mempty)
                        return (map HardegreeSL r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI","UD", "∀O", "AO", "∃I", "EI"
                                                         , "∃O", "EO", "~∃O","-∃O" ,"-EO"
                                                         , "~EO","~∀O","~AO","-∀O","-AO","QN"])
                         case r of 
                            r | r `elem` ["∀I","AI","UD"] -> return [UI]
                              | r `elem` ["∀O","AO"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃O","EO"] -> return [EE]
                              | r `elem` ["~∃O","-∃O" ,"-EO", "~EO"] -> return [NEO]
                              | r `elem` ["~∀O","~AO","-∀O","-AO"]   -> return [NUO]
                              | r `elem` ["QN"] -> return [QN1,QN2,QN3,QN4]

parseHardegreePLProof ::  RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine HardegreePL PureLexiconFOL (Form Bool)]
parseHardegreePLProof ders = toDeductionHardegree (parseHardegreePL ders) hardegreePLFormulaParser

hardegreePLNotation :: String -> String 
hardegreePLNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> hardegreeNotation s
    where altParser = do s <- try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          fallback = do c <- anyChar 
                        return [c]

hardegreePLCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseHardegreePLProof
    , ndProcessLine = hoProcessLineHardegree
    , ndNotation = hardegreePLNotation
    , ndParseSeq = parseSeqOver hardegreePLFormulaParser
    , ndParseForm = hardegreePLFormulaParser
    , ndProcessLineMemo = Just hoProcessLineHardegreeMemo
    }
