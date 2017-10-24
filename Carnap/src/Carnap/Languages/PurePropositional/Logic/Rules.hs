{-#LANGUAGE GADTs, FlexibleContexts, RankNTypes, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Rules where

import Text.Parsec
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Data.Typeable

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type PropSequentCalc = ClassicalSequentOver PurePropLexicon

type PropSequentCalcLex = ClassicalSequentLexOver PurePropLexicon

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema PropSequentCalc

pattern SeqP x arity      = FX (Lx2 (Lx1 (Predicate x arity)))
pattern SeqSP x arity     = FX (Lx2 (Lx2 (Predicate x arity)))
pattern SeqCon x arity    = FX (Lx2 (Lx3 (Connective x arity)))
pattern LFalsum           = FX (Lx2 (Lx6 (Connective Falsum AZero)))
pattern SeqProp n         = SeqP (Prop n) AZero
pattern SeqPhi :: Int -> PropSequentCalc (Form Bool)
pattern SeqPhi n          = SeqSP (SProp n) AZero
pattern SeqAnd            = SeqCon And ATwo
pattern SeqOr             = SeqCon Or ATwo
pattern SeqIf             = SeqCon If ATwo
pattern SeqIff            = SeqCon Iff ATwo
pattern SeqNot            = SeqCon Not AOne
pattern (:&-:) x y        = SeqAnd :!$: x :!$: y
pattern (:||-:) x y       = SeqOr  :!$: x :!$: y
pattern (:->-:) x y       = SeqIf  :!$: x :!$: y
pattern (:<->-:) x y      = SeqIff :!$: x :!$: y
pattern SeqNeg x          = SeqNot :!$: x

data PropSeqLabel = PropSeqFO | PropSeqACUI
        deriving (Eq, Ord, Show)

instance Eq (PropSequentCalc a) where
        (==) = (=*)

instance PrismBooleanConnLex PropSequentCalcLex Bool
instance PrismPropositionalContext PropSequentCalcLex Bool
instance PrismBooleanConst PropSequentCalcLex Bool
instance PrismPropLex PropSequentCalcLex Bool
instance PrismSchematicProp PropSequentCalcLex Bool

-- instance Combineable PropSequentCalc PropSeqLabel where

--     getLabel Top               = PropSeqACUI
--     getLabel (_ :+: _)         = PropSeqACUI
--     getLabel (GammaV _)        = PropSeqACUI
--     --getLabel (SA     _)        = PropSeqACUI
--     getLabel _                 = PropSeqFO

--     getAlgo PropSeqFO   = foUnifySys
--     getAlgo PropSeqACUI = acuiUnifySys

--     replaceChild (_ :&-: x)   pig 0 = unEveryPig pig :&-: x
--     replaceChild (x :&-: _)   pig 1 = x :&-: unEveryPig pig
--     replaceChild (_ :||-: x)  pig 0 = unEveryPig pig :||-: x
--     replaceChild (x :||-: _)  pig 1 = x :||-: unEveryPig pig
--     replaceChild (_ :->-: x)  pig 0 = unEveryPig pig :->-: x
--     replaceChild (x :->-: _)  pig 1 = x :->-: unEveryPig pig
--     replaceChild (_ :<->-: x) pig 0 = unEveryPig pig :<->-: x
--     replaceChild (x :<->-: _) pig 1 = x :<->-: unEveryPig pig
--     replaceChild (_ :+: x)    pig 0 = unEveryPig pig :+: x
--     replaceChild (x :+: _)    pig 1 = x :+: unEveryPig pig
--     replaceChild (_ :-: x)    pig 0 = unEveryPig pig :-: x
--     replaceChild (x :-: _)    pig 1 = x :-: unEveryPig pig
--     replaceChild (_ :|-: x)   pig 0 = unEveryPig pig :|-: x
--     replaceChild (x :|-: _)   pig 1 = x :|-: unEveryPig pig
--     replaceChild (SeqNeg _)   pig _ = SeqNeg $ unEveryPig pig
--     replaceChild (SS _ )      pig _ = SS $ unEveryPig pig 
--     replaceChild (SA _ )      pig _ = SA $ unEveryPig pig

instance ParsableLex (Form Bool) PurePropLexicon where
        langParser = purePropFormulaParser standardLetters

propSeqParser = seqFormulaParser :: Parsec String u (PropSequentCalc (Sequent (Form Bool)))

extendedPropSeqParser = parseSeqOver (purePropFormulaParser extendedLetters)

data DerivedRule = DerivedRule { conclusion :: PureForm, premises :: [PureForm]}
               deriving (Show, Eq)

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
axiom = [
        ] ∴ SA (phin 1) :|-: SS (phin 1)

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

replace :: PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> [SequentRule PurePropLexicon (Form Bool)]
replace x y = [ [GammaV 1  :|-: ss (propCtx 1 x)] ∴ GammaV 1  :|-: ss (propCtx 1 y)
              , [GammaV 1  :|-: ss (propCtx 1 y)] ∴ GammaV 1  :|-: ss (propCtx 1 x)]
    where ss = SS . liftToSequent

andCommutativity = replace (phin 1 ./\. phin 2) (phin 2 ./\. phin 1)

orCommutativity = replace (phin 1 .\/. phin 2) (phin 2 .\/. phin 1)

iffCommutativity = replace (phin 1 .<=>. phin 2) (phin 2 .<=>. phin 1)

deMorgansLaws = replace (lneg $ phin 1 ./\. phin 2) (lneg (phin 1) .\/. lneg (phin 2))
             ++ replace (lneg $ phin 1 .\/. phin 2) (lneg (phin 1) ./\. lneg (phin 2))

doubleNegation = replace (lneg $ lneg $ phin 1) (phin 1)

materialConditional = replace (phin 1 .=>. phin 2) (lneg (phin 1) .\/. phin 2)
                   ++ replace (phin 1 .\/. phin 2) (lneg (phin 1) .=>. phin 2)

biconditionalExchange = replace (phin 1 .<=>. phin 2) ((phin 1 .=>. phin 2) ./\. (phin 2 .=>. phin 1))

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

-- XXX slight variation from Hardegree's rule, which has weird ad-hoc syntax.
separationOfCases :: Int -> BooleanRule lex b
separationOfCases n = (GammaV 0 :|-: SS (premSuc n)
                    : take n (map premiseForm [1 ..]))
                    ∴ concAnt n :|-: SS (phin 0)
    where premSuc m = foldr (.∨.) (phin 1) (take (m - 1) $ map phin [2 ..])
          premiseForm m = GammaV m :+: SA (phin m) :|-: SS (phin 0)
          concAnt m = foldr (:+:) (GammaV 0) (take m $ map GammaV [1 ..])
