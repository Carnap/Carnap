{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Cortens
    (parseCortensQL,  parseCortensQLProof, CortensQL, cortensQLCalc) where

import Data.Map as M (lookup, Map)
import Data.Maybe (catMaybes)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,occurs)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Cortens (CortensSL, parseCortensSL, cortensSLCalc)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.PureFirstOrder.Logic.Rules

data CortensQL = SL CortensSL | AllI | AllE | ExistI | ExistE 
               | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])

instance Show CortensQL where
        show (SL x) = show x
        show (Pr _) = "PR"
        show AllI = "∀I"
        show AllE = "∀E"
        show ExistI = "∃I"
        show ExistE = "∃E"

instance Inference CortensQL PureLexiconFOL (Form Bool) where
        ruleOf (Pr _)  = axiom
        ruleOf AllI    = universalGeneralization
        ruleOf AllE    = universalInstantiation
        ruleOf ExistI  = existentialGeneralization
        ruleOf ExistE  = existentialInstantiation

        premisesOf (SL x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)
        
        conclusionOf (SL x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        isPremise (Pr _) = True
        isPremise _ = False

        isAssumption (SL x) = isAssumption x
        isAssumption _ = False

        indirectInference (SL x) = indirectInference x
        indirectInference x = Nothing

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n ExistE = Just $ cortensExistentialConstraint n ded tau
        globalRestriction (Left ded) n AllI = Just $ cortensUniversalConstraint n ded tau f
            where f :: ClassicalSequentOver PureLexiconFOL (Form Bool)
                  f = lall "v" $ phi 1
        globalRestriction _ _ _ = Nothing

cortensExistentialConstraint n ded t sub 
    | any (occurs t') priorForms = Just $ "You're instantiating this formula with a constant that appears on a prior line."
    | otherwise = case theConclusion of 
                    Just f' | t' `occurs` f' -> Just $ "You're instantiating this formula with a constant that appears in the conclusion of this proof."
                    _ -> Nothing
    where t' = applySub sub t
          priorLines = take (n - 1) ded 
          priorForms = catMaybes . map (fmap liftToSequent . assertion) $ priorLines
          finalLine = last ded 
          theConclusion = liftToSequent <$> assertion finalLine

cortensUniversalConstraint n ded t f sub 
    | any (occurs t') priorPremises = Just $ "You're generalizing with a constant that appears in a prior premise"
    | any (occurs t') priorAssumptions = Just $ "You're generalizing with a constant that appears in an active assumption"
    | any (occurs t') priorExistential = Just $ "You're generalizing with a constant that appears in an existentially derived line"
    | t' `occurs` f' = Just $ "You're generalizing with a constant that already appears in this formula"
    | otherwise = Nothing
    where t' = applySub sub t
          f' = applySub sub f
          priorExistential = catMaybes . map getForm . filter (\x -> isExistential (justificationOf x)) $ take (n - 1) ded 
          priorPremises = catMaybes . map getForm . filter (\x -> isPremiseJust (justificationOf x)) $ take (n - 1) ded 
          priorAssumptions = catMaybes . map getForm . filter (\x -> isAssumptionJust (justificationOf x)) $ take (n - 1) ded 
          getForm = fmap liftToSequent . assertion
          isExistential (Just [ExistE]) = True
          isExistential _ = False
          isPremiseJust (Just [x]) = isPremise x
          isPremiseJust _ = False
          isAssumptionJust (Just [x]) = isAssumption x
          isAssumptionJust _ = False

parseCortensQL rtc = try quantRule <|> liftProp 
    where liftProp =  map SL <$> parseCortensSL (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [AllI]
                              | r `elem` ["∀E","AE"] -> return [AllE]
                              | r `elem` ["∃I","EI"] -> return [ExistI]
                              | r `elem` ["∃E","EE"] -> return [ExistE]
                              | r == "PR" -> return [Pr (problemPremises rtc)]

parseCortensQLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) 
                     -> String -> [DeductionLine CortensQL PureLexiconFOL (Form Bool)]
parseCortensQLProof rtc = toDeductionFitchAlt (parseCortensQL rtc) cortensQLFormulaParser

cortensQLNotation :: String -> String 
cortensQLNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> s
    where altparser = do s <- try handleatom <|> handleschema <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handleatom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          handleschema = (char 'φ' >> return "◯")
                  <|> (char 'ψ' >> return "□")
                  <|> (char 'χ' >> return "△")
          fallback = do c <- anyChar 
                        return [c]

cortensQLCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseCortensQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver cortensQLFormulaParser
    , ndParseForm = cortensQLFormulaParser
    , ndNotation = cortensQLNotation
    }
