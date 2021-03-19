{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Hausman (hausmanPLCalc,parseHausmanPL) where

import Data.Maybe (catMaybes)
import Control.Lens
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,subst,FirstOrder)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser (parseSeqOver)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint,axiom)

data HausmanPL = SL P.HausmanSL | UI | UE 
                 | EI | EE 
                 | QN1 | QN2 | QN3 | QN4
                 | ID1 | ID2 | IR
                 | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                 deriving Eq

instance Show HausmanPL where
        show (SL x) = show x
        show UI          = "UG"
        show UE          = "UI"
        show EI          = "EG"
        show EE          = "EI"
        show QN1         = "QN"
        show QN2         = "QN"
        show QN3         = "QN"
        show QN4         = "QN"
        show ID1         = "ID"
        show ID2         = "ID"
        show IR          = "IR"
        show (Pr _)      = "PR"

instance Inference HausmanPL PureLexiconFOL (Form Bool) where

         ruleOf UI   = universalGeneralization
         ruleOf UE   = universalInstantiation
         ruleOf EI   = existentialGeneralization
         ruleOf EE   = existentialInstantiation
         ruleOf QN1  = quantifierNegationReplace !! 0
         ruleOf QN2  = quantifierNegationReplace !! 1
         ruleOf QN3  = quantifierNegationReplace !! 2
         ruleOf QN4  = quantifierNegationReplace !! 3
         ruleOf ID1  = leibnizLawVariations !! 0
         ruleOf ID2  = leibnizLawVariations !! 1
         ruleOf IR   = eqReflexivity
         ruleOf (Pr _) = axiom

         premisesOf (SL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (SL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (SL x) = indirectInference x
         indirectInference x = Nothing

         restriction (Pr prems) = Just (premConstraint prems)
         restriction UI = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
         restriction _ = Nothing

         globalRestriction (Left ded) n UI = Just (hausmanUniversalConstraint [tau] ded n)
         globalRestriction (Left ded) n EE = Just (hausmanExistentialConstraint [tau] ded n)
         globalRestriction _ _ _ = Nothing

         isAssumption (SL x) = isAssumption x
         isAssumption _ = False

hausmanExistentialConstraint cs ded lineno sub 
    | any (\x -> any (occursIn x) relevantForms) cs' = 
        Just $ "a variable in " ++ show cs' ++ " occurs before this line. This rule requires a variable not occuring free on any earlier line"
    | any (\x -> preview _varLabel x == Nothing) cs' = Just $ "one if " ++ show cs' ++ " is not a variable"
    | otherwise = Nothing
    where cs' = map (fromSequent . applySub sub) cs
          relevantLines = take (lineno - 1) ded
          relevantForms = catMaybes $ map assertion relevantLines
          occursIn x y = not (subst x (static 0) y =* y)

hausmanUniversalConstraint cs ded lineno sub 
    | any (\x -> any (occursIn x) relevantForms) cs' = 
        Just $ "a variable in " ++ show cs' ++ " occurs on an EI line before this one. This rule requires a variable not occuring on an EI line."
    | any (\x -> preview _varLabel x == Nothing) cs' = Just $ "one if " ++ show cs' ++ " is not a variable"
    | otherwise = Nothing
    where cs' = map (fromSequent . applySub sub) cs
          relevantLines = filter (\x -> justificationOf x == Just [EE]) $ take (lineno - 1) ded 
          relevantForms = catMaybes $ map assertion relevantLines
          occursIn x y = not (subst x (static 0) y =* y)

parseHausmanPL rtc = try quantRule <|> liftProp 
    where liftProp = do r <- P.parseHausmanSL (defaultRuntimeDeductionConfig)
                        return (map SL r)
          quantRule = do r <- choice (map (try . string) ["UG", "UI", "EG", "EI", "QN", "ID", "IR", "p"])
                         case r of 
                            "UG" -> return [UI]
                            "UI" -> return [UE]
                            "EG" -> return [EI]
                            "EI" -> return [EE]
                            "QN" -> return [QN1,QN2,QN3,QN4]
                            "ID" -> return [ID1,ID2]
                            "IR" -> return [IR]
                            "p"  -> return [Pr (problemPremises rtc)]

parseHausmanPLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine HausmanPL PureLexiconFOL (Form Bool)]
parseHausmanPLProof rtc = toCommentedDeductionFitch (parseHausmanPL rtc) hausmanPLFormulaParser --XXX Check parser

hausmanPLCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseHausmanPLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver hausmanPLFormulaParser
    , ndParseForm = hausmanPLFormulaParser
    , ndNotation = ndNotation P.hausmanSLCalc
    }
