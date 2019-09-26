{-#LANGUAGE GADTs, FlexibleContexts, RankNTypes, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Rules where

import Text.Parsec
import Data.List
import Data.Maybe (catMaybes)
import Control.Lens (toListOf, view)
import Carnap.Calculi.NaturalDeduction.Syntax
import Data.Typeable
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Types
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type PropSequentCalc = ClassicalSequentOver PurePropLexicon

type PropSequentCalcLex = ClassicalSequentLexOver PurePropLexicon

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema PropSequentCalc

data PropSeqLabel = PropSeqFO | PropSeqACUI
        deriving (Eq, Ord, Show)

instance Eq (PropSequentCalc a) where
        (==) = (=*)

premConstraint Nothing _ = Nothing
premConstraint (Just prems) sub | theinstance `elem` prems = Nothing
                                | otherwise = Just (show (project theinstance) ++ " is not one of the premises " 
                                                                               ++ intercalate ", " (map (show . project) prems))
    where theinstance = pureBNF . applySub sub $ (SA (phin 1) :|-: SS (phin 1))
          project = view rhs

dischargeConstraint n ded lhs sub | all (`elem` forms) lhs' && all (`elem` lhs') forms = Nothing
                                  | otherwise = Just $ "Some of the stated dependencies in " ++ show forms ++ ", are not among the inferred dependencies " ++ show lhs' ++ "."
    where lhs' = toListOf concretes . applySub sub $ lhs
          scope = inScope (ded !! (n - 1))
          forms = catMaybes . map (\n -> liftToSequent <$> assertion (ded !! (n - 1))) $ scope

-------------------------
--  1.1 Standard Rules  --
-------------------------
--Rules found in many systems of propositional logic

type BooleanRule lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        ) => SequentRule lex (Form b)

modusPonens :: BooleanRule lex b
modusPonens = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
              , GammaV 2 :|-: SS (phin 1)
              ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)

modusTollens :: BooleanRule lex b
modusTollens = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
               , GammaV 2 :|-: SS (lneg $ phin 2)
               ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)

axiom :: BooleanRule lex b
axiom = [] ∴ SA (phin 1) :|-: SS (phin 1)

explosion :: Int -> BooleanRule lex b
explosion n = map (\m -> GammaV m :|-: SS (phin m)) [1 .. n]
              ∴ concAnt :|-: SS (phin (n + 1))
    where concAnt = foldr (:+:) Top (map GammaV [1 .. n])

exfalso :: BooleanRule lex b
exfalso = [ GammaV 1 :|-: SS (phin 1)
          , GammaV 2 :|-: SS (lneg $ phin 1)
          ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)

identityRule :: BooleanRule lex b
identityRule = [ GammaV 1 :|-: SS (phin 1) 
               ] ∴ GammaV 1 :|-: SS (phin 1)

doubleNegationElimination :: BooleanRule lex b
doubleNegationElimination = [ GammaV 1 :|-: SS (lneg $ lneg $ phin 1) 
                            ] ∴ GammaV 1 :|-: SS (phin 1) 

doubleNegationIntroduction :: BooleanRule lex b
doubleNegationIntroduction = [ GammaV 1 :|-: SS (phin 1) 
                             ] ∴ GammaV 1 :|-: SS (lneg $ lneg $ phin 1) 

falsumElimination :: BooleanRule lex b
falsumElimination = [ GammaV 1 :|-: SS lfalsum
                    ] ∴ GammaV 1 :|-: SS (phin 1)

falsumIntroduction :: BooleanRule lex b
falsumIntroduction = [ GammaV 1 :|-: SS (lneg $ phin 1)
                     , GammaV 2 :|-: SS (phin 1)
                     ] ∴ GammaV 1 :+: GammaV 2 :|-: SS lfalsum

adjunction :: BooleanRule lex b
adjunction = [ GammaV 1  :|-: SS (phin 1) 
             , GammaV 2  :|-: SS (phin 2)
             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1 .∧. phin 2)

conditionalToBiconditional :: BooleanRule lex b
conditionalToBiconditional = [ GammaV 1  :|-: SS (phin 1 .→. phin 2)
                             , GammaV 2  :|-: SS (phin 2 .→. phin 1) 
                             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1 .↔. phin 2)

biconditionalToTwoConditional :: BooleanRule lex b
biconditionalToTwoConditional = [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                                ] ∴ GammaV 1 :|-: SS ((phin 1 .→. phin 2) .∧. (phin 2 .→. phin 1))

dilemma :: BooleanRule lex b
dilemma = [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
          , GammaV 2 :|-: SS (phin 1 .→. phin 3)
          , GammaV 3 :|-: SS (phin 2 .→. phin 3)
          ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)

hypotheticalSyllogism :: BooleanRule lex b
hypotheticalSyllogism = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
                        , GammaV 2 :|-: SS (phin 2 .→. phin 3)
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1 .→. phin 3)

---------------------------
--  1.2 Variation Rules  --
---------------------------
-- Rules with several variations

type BooleanRuleVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        ) => [SequentRule lex (Form b)]

------------------------------
--  1.2.1 Simple Variation  --
------------------------------

modusTollendoPonensVariations :: BooleanRuleVariants lex b
modusTollendoPonensVariations = [
                [ GammaV 1  :|-: SS (lneg $ phin 1) 
                , GammaV 2  :|-: SS (phin 1 .∨. phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            , 
                [ GammaV 1  :|-: SS (lneg $ phin 1) 
                , GammaV 2  :|-: SS (phin 2 .∨. phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ]

constructiveReductioVariations :: BooleanRuleVariants lex b
constructiveReductioVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                , GammaV 2 :+: SA (phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,

                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                , GammaV 2 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,

                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2 :+: SA (phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2  :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ]

explictConstructiveConjunctionReductioVariations :: BooleanRuleVariants lex b
explictConstructiveConjunctionReductioVariations = [
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :+: SA (phin 1) :|-: SS ((lneg $ phin 2) .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :|-: SS ((lneg $ phin 2) .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ]

explictNonConstructiveConjunctionReductioVariations :: BooleanRuleVariants lex b
explictNonConstructiveConjunctionReductioVariations = [
                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1) 
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1) 
                , GammaV 1 :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ]

explicitConstructiveFalsumReductioVariations :: BooleanRuleVariants lex b
explicitConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS lfalsum
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ]

explicitNonConstructiveFalsumReductioVariations :: BooleanRuleVariants lex b
explicitNonConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS lfalsum
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ]

nonConstructiveReductioVariations :: BooleanRuleVariants lex b
nonConstructiveReductioVariations = [
                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS (phin 2) 
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ,

                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS (phin 2) 
                , GammaV 2 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ,

                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2  :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( phin 1)
            ]

conditionalProofVariations :: BooleanRuleVariants lex b
conditionalProofVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2) 
            ,   [ GammaV 1 :|-: SS (phin 2) ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2)
            ]

explicitConditionalProofVariations :: BooleanRuleVariants lex b
explicitConditionalProofVariations = [
                [ GammaV 1 :+: SA (phin 1)  :|-: SS (phin 2) 
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2) 
            ,   [ GammaV 1 :|-: SS (phin 2) 
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2)
            ]

simplificationVariations :: BooleanRuleVariants lex b
simplificationVariations = [
                [ GammaV 1  :|-: SS (phin 1 .∧. phin 2) ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 1 .∧. phin 2) ] ∴ GammaV 1 :|-: SS (phin 2)
            ]

additionVariations :: BooleanRuleVariants lex b
additionVariations = [
                [ GammaV 1  :|-: SS (phin 1) ] ∴ GammaV 1 :|-: SS (phin 2 .∨. phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 1) ] ∴ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
            ]

biconditionalToConditionalVariations :: BooleanRuleVariants lex b
biconditionalToConditionalVariations = [
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2) ] ∴ GammaV 1 :|-: SS (phin 2 .→. phin 1)
            , 
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2) ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2)
            ]

proofByCasesVariations :: BooleanRuleVariants lex b
proofByCasesVariations = [
                [ GammaV 1  :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :+: SA (phin 1) :|-: SS (phin 3)
                , GammaV 3 :+: SA (phin 2) :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            ,   
                [ GammaV 1  :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :|-: SS (phin 3)
                , GammaV 3 :+: SA (phin 2) :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            ,   
                [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :+: SA (phin 1) :|-: SS (phin 3)
                , GammaV 3 :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            , 
                [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :|-: SS (phin 3)
                , GammaV 3 :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            ]

explicitProofByCasesVariations :: BooleanRuleVariants lex b
explicitProofByCasesVariations = map addExplic proofByCasesVariations
    where addExplic (SequentRule upper lower) = SequentRule (upper ++ [SA (phin 1) :|-: SS (phin 1), SA (phin 2) :|-: SS (phin 2)]) lower

tertiumNonDaturVariations :: BooleanRuleVariants lex b
tertiumNonDaturVariations = [
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ,   
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ,   
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            , 
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ]

biconditionalProofVariations :: BooleanRuleVariants lex b
biconditionalProofVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :+: SA (phin 2) :|-: SS (phin 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            ,
                [ GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :+: SA (phin 2) :|-: SS (phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            ,
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            , 
                [ GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            ]

biconditionalPonensVariations :: BooleanRuleVariants lex b
biconditionalPonensVariations = [
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2  :|-: SS (phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ,
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2  :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ]

materialConditionalVariations :: BooleanRuleVariants lex b
materialConditionalVariations =  [
                [ GammaV 1 :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 2 .→. phin 1)
            ,
                [ GammaV 1 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 2 .→. phin 1)
            ]

negatedConditionalVariations :: BooleanRuleVariants lex b
negatedConditionalVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .→. phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 1 .∧. lneg (phin 2))
            ,
                [ GammaV 1 :|-: SS (phin 1 .∧. lneg (phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .→. phin 2)
            ]

negatedConjunctionVariations :: BooleanRuleVariants lex b
negatedConjunctionVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. lneg (phin 2))
            ,
                [ GammaV 1 :|-: SS (phin 1 .→. lneg (phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .∧. phin 2)
            ]

negatedBiconditionalVariations :: BooleanRuleVariants lex b
negatedBiconditionalVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .↔. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg (phin 1) .↔. phin 2)
            ,
                [ GammaV 1 :|-: SS (lneg (phin 1) .↔. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .↔. phin 2)
            ]

deMorgansNegatedOr :: BooleanRuleVariants lex b
deMorgansNegatedOr = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∨. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg (phin 1) .∧. lneg (phin 2))
            ,
                [ GammaV 1 :|-: SS (lneg (phin 1) .∧. lneg (phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .∨. phin 2)
            ]

-------------------------------
--  1.2.2 Replacement Rules  --
-------------------------------

type ReplacementBooleanVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        , IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b))
        ) => [SequentRule lex (Form b)]

replace :: ( Typeable b, IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b))
        ) => ClassicalSequentOver lex (Form b) -> ClassicalSequentOver lex (Form b) -> [SequentRule lex (Form b)]
replace x y = [ [GammaV 1  :|-: SS (propCtx 1 x)] ∴ GammaV 1  :|-: SS (propCtx 1 y)
              , [GammaV 1  :|-: SS (propCtx 1 y)] ∴ GammaV 1  :|-: SS (propCtx 1 x)]

exchange :: Typeable b => ClassicalSequentOver lex (Form b) -> ClassicalSequentOver lex (Form b) -> [SequentRule lex (Form b)]
exchange x y = [ [GammaV 1  :|-: SS x] ∴ GammaV 1  :|-: SS y, [GammaV 1  :|-: SS y] ∴ GammaV 1  :|-: SS x]

andCommutativity :: ReplacementBooleanVariants lex b
andCommutativity = replace (phin 1 ./\. phin 2) (phin 2 ./\. phin 1)

andAssociativity :: ReplacementBooleanVariants lex b
andAssociativity = replace ((phin 1 ./\. phin 2) ./\. phin 3) (phin 1 ./\. (phin 2 ./\. phin 3))

andIdempotence :: ReplacementBooleanVariants lex b
andIdempotence = replace (phin 1 ./\. phin 1) (phin 1)

orCommutativity :: ReplacementBooleanVariants lex b
orCommutativity = replace (phin 1 .\/. phin 2) (phin 2 .\/. phin 1)

orAssociativity :: ReplacementBooleanVariants lex b
orAssociativity = replace ((phin 1 .\/. phin 2) .\/. phin 3) (phin 1 .\/. (phin 2 .\/. phin 3))

orIdempotence :: ReplacementBooleanVariants lex b
orIdempotence = replace (phin 1 .\/. phin 1) (phin 1)

iffCommutativity :: ReplacementBooleanVariants lex b
iffCommutativity = replace (phin 1 .<=>. phin 2) (phin 2 .<=>. phin 1)

deMorgansLaws :: ReplacementBooleanVariants lex b
deMorgansLaws = replace (lneg $ phin 1 ./\. phin 2) (lneg (phin 1) .\/. lneg (phin 2))
             ++ replace (lneg $ phin 1 .\/. phin 2) (lneg (phin 1) ./\. lneg (phin 2))

doubleNegation :: ReplacementBooleanVariants lex b
doubleNegation = replace (lneg $ lneg $ phin 1) (phin 1)

materialConditional :: ReplacementBooleanVariants lex b
materialConditional = replace (phin 1 .=>. phin 2) (lneg (phin 1) .\/. phin 2)
                   ++ replace (phin 1 .\/. phin 2) (lneg (phin 1) .=>. phin 2)

negatedConditional :: ReplacementBooleanVariants lex b
negatedConditional = replace (lneg $ phin 1 .=>. phin 2) (phin 1 ./\. (lneg $ phin 2))

contraposition :: ReplacementBooleanVariants lex b
contraposition = replace (phin 1 .=>. phin 2) (lneg (phin 2) .=>. lneg (phin 1))

exportation :: ReplacementBooleanVariants lex b
exportation = replace (phin 1 .=>. (phin 2 .=>. phin 3)) ((phin 1 ./\. phin 2) .=>. phin 3)

distribution :: ReplacementBooleanVariants lex b
distribution = replace (phin 1 ./\. (phin 2 .\/. phin 3)) ((phin 1 ./\. phin 2) .\/. (phin 1 ./\. phin 3)) ++ replace (phin 1 .\/. (phin 2 ./\. phin 3)) ((phin 1 .\/. phin 2) ./\. (phin 1 .\/. phin 3))

biconditionalExchange :: ReplacementBooleanVariants lex b
biconditionalExchange = replace (phin 1 .<=>. phin 2) ((phin 1 .=>. phin 2) ./\. (phin 2 .=>. phin 1))

biconditionalCases :: ReplacementBooleanVariants lex b
biconditionalCases = replace (phin 1 .<=>. phin 2) ((phin 1 ./\. phin 2) .\/. (lneg (phin 2) ./\. lneg (phin 1)))


----------------------------------------
--  1.2.3 Infinitary Variation Rules  --
----------------------------------------

-- rules with an infnite number of schematic variations

-- XXX at the moment, these requires all assumptions to be used. Should
-- actually be parameterized by l::[Bool] of length n rather than n::Int
-- or alternately, the checking mechanism should be modified to allow
-- weakening.

eliminationOfCases :: Int -> BooleanRule lex b
eliminationOfCases n = (premAnt n :|-: SS lfalsum
                     : take n (map premiseForm [1 ..]))
                     ∴ GammaV 1 :|-: SS (concSuc n)
    where premiseForm m = SA (lneg $ phin m) :|-: SS (lneg $ phin m)
          premAnt m = foldr (:+:) (GammaV 1) (take m $ map (SA . lneg . phin) [1 ..])
          concSuc m = foldr (.∨.) (phin 1) (take (m - 1) $ map phin [2 ..])

-- XXX slight syntactic variation from Hardegree's rule.
separationOfCases :: Int -> BooleanRule lex b
separationOfCases n = (GammaV 0 :|-: SS (premSuc n)
                    : take n (map premiseForm [1 ..]))
                    ∴ concAnt n :|-: SS (phin 0)
    where premSuc m = foldr (.∨.) (phin 1) (take (m - 1) $ map phin [2 ..])
          premiseForm m = GammaV m :+: SA (phin m) :|-: SS (phin 0)
          concAnt m = foldr (:+:) (GammaV 0) (take m $ map GammaV [1 ..])

explicitSeparationOfCases :: Int -> BooleanRule lex b
explicitSeparationOfCases n = (GammaV 0 :|-: SS (premSuc n)
                            : map premiseForm [1 .. n]
                            ++ map assumptionForm [1 .. n])
                            ∴ concAnt n :|-: SS (phin 0)
    where premSuc m = foldr (.∨.) (phin 1) (take (m - 1) $ map phin [2 ..])
          premiseForm m = GammaV m :+: SA (phin m) :|-: SS (phin 0)
          assumptionForm m = SA (phin m) :|-: SS (phin m)
          concAnt m = foldr (:+:) (GammaV 0) (take m $ map GammaV [1 ..])
