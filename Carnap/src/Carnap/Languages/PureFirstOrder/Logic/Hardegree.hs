{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Hardegree (hardegreePL2006Calc, hardegreePLCalc,parseHardegreePL)
where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Languages.PurePropositional.Logic.Hardegree (hardegreeNotation)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineHardegreeMemo, hoProcessLineHardegree)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.PureFirstOrder.Logic.Rules

--------------------
--  1. System PL  --
--------------------

data HardegreePLCore = UI | UE | EI | EE | NUO | NEO 
                | PR (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                deriving Eq

-- A system of first-order logic resembling system PL from Hardegree's
-- 2016 Introduction to Modal Logic
data HardegreePL = HardegreeSL P.HardegreeSL | PLCore HardegreePLCore | QN1 | QN2 | QN3 | QN4
                 deriving Eq

-- A system of first-order logic resembling system PL from Hardegree's
-- 2006 First Steps book
data HardegreePL2006 = HardegreeSL2006 P.HardegreeSL2006 | PLCore2006 HardegreePLCore | ED1 | ED2
                 deriving Eq

instance Show HardegreePLCore where
        show UI          = "UD"
        show UE          = "∀O"
        show EI          = "∃I"
        show EE          = "∃O"
        show NUO         = "~∀O"
        show NEO         = "~∃O"
        show (PR _)      = "PR"

instance Show HardegreePL where
        show (HardegreeSL x) = show x
        show (PLCore x) = show x
        show QN1         = "QN"
        show QN2         = "QN"
        show QN3         = "QN"
        show QN4         = "QN"

instance Show HardegreePL2006 where
        show (HardegreeSL2006 x) = show x
        show (PLCore2006 x) = show x
        show ED1        = "∃D"
        show ED2        = "∃D"

instance Inference HardegreePLCore PureLexiconFOL (Form Bool) where

         ruleOf (PR _)  = axiom
         ruleOf UI      = universalGeneralization
         ruleOf UE      = universalInstantiation
         ruleOf EI      = existentialGeneralization
         ruleOf EE      = existentialInstantiation
         ruleOf NUO     = negatedUniversalInstantiation
         ruleOf NEO     = negatedExistentialInstantiation

         premisesOf r = upperSequents (ruleOf r)

         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference UI = Just (TypedProof (ProofType 0 1)) 
         indirectInference _ = Nothing

         globalRestriction (Left ded) n EE = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n UI = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n NUO = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction _ _ _ = Nothing

         restriction (PR prems) = Just (premConstraint prems)
         restriction _ = Nothing

         isAssumption _ = False

instance Inference HardegreePL PureLexiconFOL (Form Bool) where

         ruleOf (PLCore x) = ruleOf x
         ruleOf QN1  = quantifierNegation !! 0
         ruleOf QN2  = quantifierNegation !! 1
         ruleOf QN3  = quantifierNegation !! 2
         ruleOf QN4  = quantifierNegation !! 3

         premisesOf (HardegreeSL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)

         conclusionOf (HardegreeSL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (HardegreeSL x) = indirectInference x
         indirectInference (PLCore x) = indirectInference x
         indirectInference _ = Nothing

         globalRestriction (Left ded) n (PLCore EE) = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n (PLCore UI) = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n (PLCore NUO) = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction _ _ _ = Nothing

         restriction (PLCore x) = restriction x
         restriction _ = Nothing

         isAssumption (HardegreeSL x) = isAssumption x
         isAssumption _ = False

instance Inference HardegreePL2006 PureLexiconFOL (Form Bool) where

         ruleOf (PLCore2006 NEO) = quantifierNegation !! 0
         ruleOf (PLCore2006 NUO) = quantifierNegation !! 3
         ruleOf ED1 = explicitNonConstructiveFalsumReductioVariations !! 0
         ruleOf ED2 = explicitNonConstructiveFalsumReductioVariations !! 1
         ruleOf (PLCore2006 x) = ruleOf x

         premisesOf (HardegreeSL2006 x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)

         conclusionOf (HardegreeSL2006 x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (HardegreeSL2006 x) = indirectInference x
         indirectInference (PLCore2006 x) = indirectInference x
         indirectInference ED1 = Just assumptiveProof
         indirectInference ED2 = Just assumptiveProof
         indirectInference _ = Nothing

         restriction (PLCore2006 x) = restriction x
         restriction _ = Nothing

         globalRestriction (Left ded) n (PLCore2006 EE) = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n (PLCore2006 UI) = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction _ _ _ = Nothing

         isAssumption (HardegreeSL2006 x) = isAssumption x
         isAssumption _ = False

parseHardegreePL rtc = try quantRule <|> liftProp
    where liftProp = map HardegreeSL <$> P.parseHardegreeSL (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI","UD", "∀O", "AO", "∃I", "EI"
                                                         , "∃O", "EO", "~∃O","-∃O" ,"-EO"
                                                         , "~EO","~∀O","~AO","-∀O","-AO","QN", "PR"])
                         return $ case r of
                            r | r `elem` ["∀I","AI","UD"] -> [PLCore UI]
                              | r `elem` ["∀O","AO"] -> [PLCore UE]
                              | r `elem` ["∃I","EI"] -> [PLCore EI]
                              | r `elem` ["∃O","EO"] -> [PLCore EE]
                              | r `elem` ["~∃O","-∃O" ,"-EO", "~EO"] -> [PLCore NEO]
                              | r `elem` ["~∀O","~AO","-∀O","-AO"] -> [PLCore NUO]
                              | r == "QN" -> [QN1,QN2,QN3,QN4]
                              | r == "PR" -> [PLCore (PR (problemPremises rtc))]

parseHardegreePL2006 rtc = try quantRule <|> liftProp
    where liftProp = map HardegreeSL2006 <$> P.parseHardegreeSL2006 (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["UD", "∀O", "AO", "∃I", "EI","ED"
                                                         ,"∃D", "∃O", "EO", "~∃O","-∃O" ,"-EO"
                                                         , "~EO","~∀O","~AO","-∀O","-AO", "PR"])
                         return $ case r of 
                            r | r `elem` ["UD"] -> [PLCore2006 UI]
                              | r `elem` ["∀O","AO"] -> [PLCore2006 UE]
                              | r `elem` ["∃I","EI"] -> [PLCore2006 EI]
                              | r `elem` ["∃O","EO"] -> [PLCore2006 EE]
                              | r `elem` ["~∃O","-∃O" ,"-EO", "~EO"] -> [PLCore2006 NEO]
                              | r `elem` ["~∀O","~AO","-∀O","-AO"] -> [PLCore2006 NUO]
                              | r `elem` ["ED", "∃D"] -> [ED1,ED2]
                              | r == "PR" -> [PLCore2006 (PR (problemPremises rtc))]

parseHardegreePLProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine HardegreePL PureLexiconFOL (Form Bool)]
parseHardegreePLProof ders = toDeductionHardegree (parseHardegreePL ders) hardegreePLFormulaParser

parseHardegreePL2006Proof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine HardegreePL2006 PureLexiconFOL (Form Bool)]
parseHardegreePL2006Proof ders = toDeductionHardegree (parseHardegreePL2006 ders) hardegreePLFormulaParser

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

hardegreePL2006Calc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseHardegreePL2006Proof
    , ndProcessLine = hoProcessLineHardegree
    , ndNotation = hardegreePLNotation
    , ndParseSeq = parseSeqOver hardegreePLFormulaParser
    , ndParseForm = hardegreePLFormulaParser
    , ndProcessLineMemo = Just hoProcessLineHardegreeMemo
    }
