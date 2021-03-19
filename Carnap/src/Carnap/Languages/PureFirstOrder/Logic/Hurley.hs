{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Hurley (hurleyPLCalc, parseHurleyPL) where

import Data.Map as M (lookup, Map,empty)
import Data.Maybe
import Text.Parsec
import Control.Lens
import Carnap.Core.Data.Types (Form, Term)
import Carnap.Core.Data.Optics (liftLang)
import Carnap.Core.Unification.Unification
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic.Hurley as P
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PureFirstOrder.Util
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

data HurleyPL = SL P.HurleySL | UI | UG | EG
              | EI (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
              | QN1 | QN2 | QN3 | QN4 | QN5 | QN6 | QN7 | QN8 | Id1 | Id2 | Id3 | Id4
              | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
              deriving Eq

instance Show HurleyPL where
        show (SL x) = show x 
        show UI  = "UI"
        show UG  = "UG"
        show (EI _)  = "EI"
        show EG  = "EG"
        show QN1 = "QN"
        show QN2 = "QN"
        show QN3 = "QN"
        show QN4 = "QN"
        show QN5 = "QN"
        show QN6 = "QN"
        show QN7 = "QN"
        show QN8 = "QN"
        show Id1 = "Id"
        show Id2 = "Id"
        show Id3 = "Id"
        show Id4 = "Id"
        show (Pr _) = ""

instance Inference HurleyPL PureLexiconFOL (Form Bool) where

        ruleOf  UI  = universalInstantiation
        ruleOf  UG  = universalGeneralization
        ruleOf  (EI _)  = existentialInstantiation
        ruleOf  EG = existentialGeneralization
        ruleOf  QN1 = quantifierNegationReplace !! 0
        ruleOf  QN2 = quantifierNegationReplace !! 1
        ruleOf  QN3 = quantifierNegationReplace !! 2
        ruleOf  QN4 = quantifierNegationReplace !! 3
        ruleOf  QN5 = quantifierDoubleNegationReplace !! 0
        ruleOf  QN6 = quantifierDoubleNegationReplace !! 1
        ruleOf  QN7 = quantifierDoubleNegationReplace !! 2
        ruleOf  QN8 = quantifierDoubleNegationReplace !! 3
        ruleOf  Id1 = eqReflexivity
        ruleOf  Id2 = leibnizLawVariations !! 0
        ruleOf  Id3 = leibnizLawVariations !! 1
        ruleOf  Id4 = eqSymmetryReplacement !! 0
        ruleOf  (Pr _) = axiom
        ruleOf x@(SL _) = SequentRule (premisesOf x) (conclusionOf x)

        premisesOf (SL x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)
        
        conclusionOf (SL x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference (SL x) = indirectInference x
        indirectInference x = Nothing

        restriction UG = Just (isVarConstraint tau)
        restriction (EI _) = Just (isConstantConstraint tau)
        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n (EI (Just prems)) = Just (freshConstantConstraint tau prems ded n)
        globalRestriction (Left ded) n (EI Nothing) = Just (freshConstantConstraint tau [] ded n)
        globalRestriction (Left ded) n (UG) = Just (existentiallyFreshConstraint tau ded n 
                                                    `andFurtherRestriction` assumptivelyFreshConstraint tau ded n)
        globalRestriction _ _ _  = Nothing

        isAssumption (SL x) = isAssumption x
        isAssumption _ = False

        isPremise (Pr _) = True
        isPremise _ = False

freshConstantConstraint c prems ded lineno sub
        | any (\x -> c' `occurs` x) theLines = Just $ "it appears that the constant " ++ show c' ++ " appears on a previous line"
        | any (\x -> c' `occurs` x) prems = Just $ "it appears that the constant " ++ show c' ++ " occurs in one of the premises"
        | otherwise = Nothing
    where c' = applySub sub c
          theLines = catMaybes . map (fmap liftLang . assertion) . take (lineno - 1) $ ded

existentiallyFreshConstraint c ded lineno sub
        | any (\x -> c' `occurs` x) theLines = Just $ "it appears that the constant " ++ show c' ++ " appears on a previous line justified by EI"
        | otherwise = Nothing
    where c' = applySub sub c
          theLines = catMaybes . map (fmap liftLang . assertion) . filter (maybe False (any isEI) . ruleOfLine) . take (lineno - 1) $ ded
          isEI (EI _) = True
          isEI _ = False

assumptivelyFreshConstraint c ded lineno sub
        | any (\x -> c' `occurs` x) theLines = Just $ "it appears that the variable " ++ show c' ++ " appears in an open assumption"
        | otherwise = Nothing
    where c' = applySub sub c
          theLines = catMaybes . map (fmap liftLang . assertion) . filter (maybe False (any isAssumption) . ruleOfLine) $ oldRelevant [] . reverse . take (lineno - 1) $ ded

          oldRelevant accum [] = accum
          oldRelevant [] (d:ded)  = oldRelevant [d] ded 
          oldRelevant (a:accum) (d:ded) = if depth d > depth a 
                                              then oldRelevant (a:accum) ded 
                                              else oldRelevant (d:a:accum) ded 

isConstantConstraint c sub
        | not . null $ preview _constIdx c' =  Nothing
        | otherwise = Just $ "it appears that the term " ++ show c' ++ "  is not a constant. But this rule requires it to be a constant."
    where c' = applySub sub c 

isVarConstraint c sub
        | not . null $ preview _varLabel c' =  Nothing
        | otherwise = Just $ "it appears that the term " ++ show c' ++ "  is not a variable. But this rule requires it to be a variable."
    where c' = applySub sub c 

parseHurleyPL rtc = do ms <- optionMaybe ((spaces >> eof >> return ()) <|>  (string "/" >> many anyChar >> return ()))
                       case ms of 
                            Just _ -> return [Pr (problemPremises rtc)]
                            Nothing -> try quantRule <|> liftProp 
    where liftProp = do r <- P.parseHurleySL (defaultRuntimeDeductionConfig)
                        return (map SL r)
          quantRule = do r <- choice (map (try . string) ["UI","UG","EG","EI","Id"])
                         case r of 
                            r | r `elem` ["UI"] -> return [UI]
                              | r `elem` ["UG"] -> return [UG]
                              | r `elem` ["EG"] -> return [EG]
                              | r `elem` ["EI"] -> return [EI (problemPremises rtc)]
                              | r `elem` ["QN"] -> return [QN1,QN2,QN3,QN4,QN5,QN6,QN7,QN8]
                              | r `elem` ["ID"] -> return [Id1,Id2,Id3,Id4]

parseHurleyPLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine HurleyPL PureLexiconFOL (Form Bool)]
parseHurleyPLProof rtc = toDeductionFitchAlt (parseHurleyPL rtc) hurleyPLFormulaParser --XXX Check parser

hurleyPLCalc = mkNDCalc
    { ndParseProof = parseHurleyPLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver hurleyPLFormulaParser
    , ndParseForm = hurleyPLFormulaParser
    , ndNotation = ndNotation P.hurleySLCalc
    }
