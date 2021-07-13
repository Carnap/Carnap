{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Tomassi where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.Types 
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,occurs)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules (dischargeConstraint, premConstraint,axiom)
import Carnap.Languages.Util.LanguageClasses (lall)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Tomassi hiding (Pr)

{-| A system for first-order logic resembling the proof system QL
from Tomassi's Logic book
-}

data TomassiQL = PL TomassiPL
               | UI    | UE
               | EI    | EE
               | EqI   | EqE 
               | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
               deriving Eq

instance Show TomassiQL where
        show (PL x) = show x
        show EI = "EI"
        show EE = "EE"
        show UI = "UI"
        show UE = "UE"
        show EqI = "=I"
        show EqE = "=E"

instance Inference TomassiQL PureLexiconFOL (Form Bool) where

        ruleOf (Pr _) = axiom
        ruleOf UI  = universalGeneralization
        ruleOf UE  = universalInstantiation
        ruleOf EI  = existentialGeneralization
        ruleOf EE  = existentialDerivation !! 0
        ruleOf EqI = eqReflexivity
        ruleOf EqE = leibnizLawVariations !! 0 --do we also want reverse?
        ruleOf r = premisesOf r ∴ conclusionOf r

        premisesOf (PL x) = map liftSequent (premisesOf x)
        premisesOf x = upperSequents (ruleOf x)

        conclusionOf (PL x) = liftSequent (conclusionOf x)
        conclusionOf x = lowerSequent (ruleOf x)

        restriction UI = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n EE = Just (onlyNewConstraint n ded tau' (phi' 1 tau') 
                                                 `andFurtherRestriction`
                                                  dischargeConstraint n ded (view lhs $ conclusionOf EE))
            where tau' :: FixLang PureLexiconFOL (Term Int)
                  tau' = tau
                                                 --make sure that any occurance of tau is ≥ the last occurance of phi 1 tau
        globalRestriction (Left ded) n (PL CP) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (PL CP)))
        globalRestriction (Left ded) n (PL RAA1) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (PL RAA1)))
        globalRestriction (Left ded) n (PL RAA2) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (PL RAA2)))
        globalRestriction (Left ded) n (PL ORE) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (PL ORE)))
        globalRestriction _ _ _ = Nothing

        isAssumption (Pr _) = True
        isAssumption (PL x) = isAssumption x
        isAssumption _ = False

onlyNewConstraint m ded term form sub = 
        case termOccurs of
            [] -> Just "Somehow, the term cited isn't in the proof"
            (n,_):_ | not ((n,n) `elem` theDeps) -> Just $ "The first occurance of " ++ show theTerm ++ ", on line " 
                                                     ++ show n ++ " isn't the cited assumption."
            (n,l):_ | assertionOf l /= (Just theForm) -> Just $ "The first occurance of " ++ show theTerm ++ ", on line " 
                                                            ++ show n ++ " isn't the cited assumption."
            (n,l):_ | checkRuleIn l  -> Just $ "The first occurance of " ++ show theTerm ++ ", on line "
                                             ++ show n ++ " isn't the cited assumption."
            _  -> Nothing
    where theDeps = maybe [] id (dependencies $ ded !! (m - 1))
          theTerm = applySub sub (liftToSequent term)
          theForm = applySub sub (liftToSequent form)
          termOccurs = filter (checkTermIn . snd) (zip [1 ..] ded)
          assertionOf l = liftToSequent <$> assertion l
          checkTermIn l = maybe False (\phi -> theTerm `occurs` liftToSequent phi) $ assertion l
          checkRuleIn l = maybe True (not . isAssumption . head) $ ruleOfLine l
    
parseTomassiQL rtc n annote = try parseProp <|> parseQuant
    where parseProp = map PL <$> parseTomassiPL (defaultRuntimeDeductionConfig) n annote
          parseQuant = do r <- choice (map (try . string) [ "UI", "UE", "EE", "EI", "=I", "=E" ])
                          return $ case r of
                                      "UI" -> [UI]
                                      "UE" -> [UE]
                                      "EE" -> [EE]
                                      "EI" -> [EI]
                                      "=I" -> [EqI]
                                      "=E" -> [EqE]

parseTomassiQLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) 
                     -> String -> [DeductionLine TomassiQL PureLexiconFOL (Form Bool)]
parseTomassiQLProof rtc = toDeductionLemmonTomassi (parseTomassiQL rtc) tomassiQLFormulaParser

tomassiQLCalc = mkNDCalc
    { ndRenderer = LemmonStyle TomassiStyle
    , ndParseProof = parseTomassiQLProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseForm = tomassiQLFormulaParser
    , ndParseSeq = parseSeqOver tomassiQLFormulaParser
    , ndNotation = tomassiPLNotation
    }
