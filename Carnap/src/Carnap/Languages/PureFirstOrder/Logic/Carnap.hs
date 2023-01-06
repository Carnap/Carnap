{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Carnap
        (FOLogic(..), parseFOLogic, folCalc, folCalcNonC)
    where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Unification.Unification (applySub)
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Carnap hiding (PR,DER)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineMontague, hoProcessLineMontagueMemo)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules (axiom,premConstraint, nonConstructiveReductioVariations)
import Carnap.Languages.PureFirstOrder.Logic.Rules

--------------------------------------------------------
--2. Classical First-Order Logic
--------------------------------------------------------

data FOLogic = SL PropLogic
             | UD  | UI  | EG  | ED1 | ED2 | QN1 | QN2  | QN3  | QN4  
             | LL1 | LL2 | EL1 | EL2 | ID  | SM  | ALL1 | ALL2
             | DER String (ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))
             | PR (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
             deriving (Eq)

data FOLogicNonC = NonC FOLogic
                 | ID5 | ID6  | ID7  | ID8
                 deriving (Eq)

instance Show FOLogic where
        show (PR _)  = "PR"
        show UD      = "UD"
        show UI      = "UI"
        show EG      = "EG"
        show ED1     = "ED"
        show ED2     = "ED"
        show (DER s _) = "D-" ++ s
        show QN1     = "QN"
        show QN2     = "QN"
        show QN3     = "QN"
        show QN4     = "QN"
        show ID      = "Id"
        show LL1     = "LL"
        show LL2     = "LL"
        show ALL1    = "LL"
        show ALL2    = "LL"
        show EL1     = "EL"
        show EL2     = "EL"
        show SM      = "Sm"
        show (SL x)  = show x

instance Show FOLogicNonC where
        show (NonC x) = show x
        show _ = "NC"

instance Inference FOLogic PureLexiconFOL (Form Bool) where
     ruleOf (PR _)    = axiom
     ruleOf UI        = universalInstantiation
     ruleOf EG        = existentialGeneralization
     ruleOf UD        = universalGeneralization
     ruleOf ED1       = existentialDerivation !! 0
     ruleOf ED2       = existentialDerivation !! 1
     ruleOf QN1       = quantifierNegation !! 0
     ruleOf QN2       = quantifierNegation !! 1
     ruleOf QN3       = quantifierNegation !! 2
     ruleOf QN4       = quantifierNegation !! 3
     ruleOf LL1       = leibnizLawVariations !! 0
     ruleOf LL2       = leibnizLawVariations !! 1
     ruleOf ALL1      = antiLeibnizLawVariations !! 0
     ruleOf ALL2      = antiLeibnizLawVariations !! 1
     ruleOf EL1       = euclidsLawVariations !! 0
     ruleOf EL2       = euclidsLawVariations !! 1
     ruleOf ID        = eqReflexivity
     ruleOf SM        = eqSymmetry
     ruleOf x@(SL _)  = premisesOf x ∴ conclusionOf x

     premisesOf (SL x) = map liftSequent (premisesOf x)
     premisesOf (DER _ r) = multiCutLeft r
     premisesOf x     = upperSequents (ruleOf x)

     conclusionOf (SL x) = liftSequent (conclusionOf x)
     conclusionOf (DER _ r) = multiCutRight r
     conclusionOf x   = lowerSequent (ruleOf x)

     restriction UD         = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
     restriction ED1        = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
     restriction ED2        = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
     restriction (PR prems) = Just (premConstraint prems)
     restriction _          = Nothing

     indirectInference (SL x) = indirectInference x
     indirectInference x
        | x `elem` [ ED1,ED2,UD ] = Just PolyProof
        | otherwise = Nothing

instance Inference FOLogicNonC PureLexiconFOL (Form Bool) where
     ruleOf ID5       = nonConstructiveReductioVariations !! 0
     ruleOf ID6       = nonConstructiveReductioVariations !! 1
     ruleOf ID7       = nonConstructiveReductioVariations !! 2
     ruleOf ID8       = nonConstructiveReductioVariations !! 3
     ruleOf (NonC x)  = ruleOf x

     premisesOf (NonC (DER _ r))  = multiCutLeft r
     premisesOf x                 = upperSequents (ruleOf x)

     conclusionOf (NonC (DER _ r))  = multiCutRight r
     conclusionOf x                 = lowerSequent (ruleOf x)

     restriction (NonC x) = restriction x
     restriction _ = Nothing

     indirectInference (NonC x) = indirectInference x
     indirectInference _ = Just PolyProof

parseFOLogic :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [FOLogic]
parseFOLogic rtc = try quantRule <|> liftProp
    where liftProp = map SL <$> parsePropLogic (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["PR", "UI", "UD", "EG", "ED", "QN","LL","EL","Id","Sm","D-"])
                         case r of 
                            r | r == "PR" -> return [PR $ problemPremises rtc]
                              | r == "UI" -> return [UI]
                              | r == "UD" -> return [UD]
                              | r == "EG" -> return [EG]
                              | r == "ED" -> return [ED1,ED2]
                              | r == "QN" -> return [QN1,QN2,QN3,QN4]
                              | r == "LL" -> return [LL1,LL2,ALL1,ALL2]
                              | r == "Sm" -> return [SM]
                              | r == "EL" -> return [EL1,EL2]
                              | r == "Id" -> return [ID]
                              | r == "D-" ->  do rn <- many1 upper
                                                 case M.lookup rn (derivedRules rtc) of
                                                    Just r  -> return [DER rn r]
                                                    Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"


parseFOLogicNonC :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [FOLogicNonC]
parseFOLogicNonC rtc = indirect <|> (map NonC <$> parseFOLogic rtc)
    where indirect = string "ID" >> return [NonC (SL ID1), NonC (SL ID2), NonC (SL ID3), NonC (SL ID4), ID5, ID6, ID7, ID8]

parseFOLProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine FOLogic PureLexiconFOL (Form Bool)]
parseFOLProof ders = toDeductionMontague (parseFOLogic ders) folFormulaParser

parseFOLNonCProof ::  RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine FOLogicNonC PureLexiconFOL (Form Bool)]
parseFOLNonCProof ders = toDeductionMontague (parseFOLogicNonC ders) folFormulaParser

folCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseFOLProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    }

folCalcNonC = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseFOLNonCProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    }
