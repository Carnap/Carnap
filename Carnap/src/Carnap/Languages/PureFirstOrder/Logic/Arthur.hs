{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Arthur (arthurQLCalc, ArthurQL(..), parseArthurQL) where

import Data.Map as M (lookup, Map,empty)
import Data.Maybe (catMaybes)
import Text.Parsec
import Control.Lens (toListOf)
import Carnap.Core.Data.Types (Form, Term, FixLang)
import Carnap.Core.Unification.Unification (applySub,occurs)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Arthur hiding (Pr)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (fitchAssumptionCheck, premConstraint,axiom)

{-| A system for quantified logic resembling the Statement Logic proof system 
from Arthur's Introduction to Logic book
-}

data ArthurQL = UI  | UG  | EI (Maybe [ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool))])
              | EG  | QN1 | QN2 | QN3 | QN4
              | SI  | RI
              | SL ArthurSL | Pr (Maybe [ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool))])
              deriving Eq

instance Show ArthurQL where
        show (Pr _) = "P"
        show (SL x) = show x
        show UI = "UI"
        show UG = "UG"
        show (EI _) = "EI"
        show EG = "EG"
        show QN1 = "QN"
        show QN2 = "QN"
        show QN3 = "QN"
        show QN4 = "QN"
        show SI  = "SI"
        show RI  = "RI"

instance Inference ArthurQL PureLexiconFOL (Form Bool) where

        ruleOf UI = universalInstantiation
        ruleOf UG = universalGeneralization
        ruleOf (EI _) = existentialInstantiation
        ruleOf EG = existentialGeneralization
        ruleOf QN1 = quantifierNegation !! 0
        ruleOf QN2 = quantifierNegation !! 1
        ruleOf QN3 = quantifierNegation !! 2
        ruleOf QN4 = quantifierNegation !! 3
        ruleOf SI  = leibnizLawVariations !! 0
        ruleOf RI  = [] ∴ Top :|-: SS (lall "v" $ \x -> x `equals'` x)
            where equals' :: ClassicalSequentOver PureLexiconFOL (Term Int) -> ClassicalSequentOver PureLexiconFOL (Term Int) 
                                -> ClassicalSequentOver PureLexiconFOL (Form Bool)
                  equals' = equals
        ruleOf (Pr _) = axiom

        restriction UG = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
        restriction _ = Nothing

        globalRestriction (Left ded) n (SL CP1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (SL CP2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (SL RA1) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]  
        globalRestriction (Left ded) n (SL RA2) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]  
        globalRestriction (Left ded) n UG = Just $ arthurUniversalConstraint n ded tau f
            where f :: ClassicalSequentOver PureLexiconFOL (Form Bool)
                  f = phi 1 tau
        globalRestriction (Left ded) n (EI (Just list)) = Just $ existentiallyFreshConstraint n ded tau list
        globalRestriction (Left ded) n (EI Nothing) = Just $ existentiallyFreshConstraint n ded tau []
        globalRestriction (Left ded) n _ = Nothing

        premisesOf (SL x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)
        
        conclusionOf (SL x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference (SL x) = indirectInference x
        indirectInference x = Nothing

        isAssumption (SL x) = isAssumption x
        isAssumption _ = False

        isPremise (Pr _) = True
        isPremise _ = False

existentiallyFreshConstraint n ded t list sub 
    | any (\x -> tau' `occurs` x) relevantLines = Just $ show tau' ++ " appears not to be fresh on line " ++ show n
    | otherwise = Nothing
    where relevantLines = map liftToSequent . catMaybes . map assertion $ (take (n - 1) ded)
          tau' = applySub sub t

arthurUniversalConstraint n ded t f sub 
    | any (occurs t') relevantFormsAfterEI = 
        Just $ "The formula you're generalizing on contains a name introduced by an application of EI to a formula involving the variable you're generalizing on"
    | otherwise = Nothing
    where t' = applySub sub t
          f' = applySub sub f
          relevantLines = filter (\x -> isExistential (justificationOf x)) $ take (n - 1) ded 
          getFirstDep (f,g) = case dependencies f of
                                  Just (x:_) -> Just (fst x, g)
                                  Nothing -> Nothing
          relevantLineDeps = map (\(m,g) -> (ded !! (m - 1) , g)) . catMaybes . map getFirstDep $ zip relevantLines relevantLines
          checkForms (k,l) = case (assertion k, assertion l) of
                                 (Just f, Just g) | t' `occurs` liftToSequent f -> Just (liftToSequent f, liftToSequent g)
                                 _ -> Nothing
          relevantForms = catMaybes . map checkForms $ relevantLineDeps
          termDifference (f,g) = [x | x <- toListOf termsOf g, not (x `elem` toListOf termsOf f)]
          relevantNames = concatMap termDifference relevantForms
          relevantFormsAfterEI = map liftToSequent . catMaybes . map assertion $ relevantLines
          isExistential (Just [EI _]) = True
          isExistential _ = False

parseArthurQL rtc = try quantRule <|> liftProp 
    where liftProp =  map SL <$> parseArthurSL defaultRuntimeDeductionConfig
          quantRule = do r <- choice (map (try . string) ["UI", "EI", "UG", "EG", "QN", "SI", "RI", "P"])
                         return $ case r of 
                            "UI" -> [UI]
                            "EI" -> [EI (problemPremises rtc)]
                            "UG" -> [UG]
                            "EG" -> [EG]
                            "QN" -> [QN1, QN2, QN3, QN4]
                            "SI" -> [SI]
                            "RI" -> [RI]
                            "P"  -> [Pr (problemPremises rtc)]

parseArthurQLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine ArthurQL PureLexiconFOL (Form Bool)]
parseArthurQLProof rtc = toDeductionFitch (parseArthurQL rtc) arthurFOLFormulaParser

arthurNotation :: String -> String 
arthurNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> dropOuterParens s
    where altparser = do s <- try handleatom <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handleatom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          fallback = do c <- anyChar 
                        return [c]

arthurQLCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseArthurQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver arthurFOLFormulaParser
    , ndParseForm = arthurFOLFormulaParser
    , ndNotation = arthurNotation
    }
