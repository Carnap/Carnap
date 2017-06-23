{-#LANGUAGE GADTs, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses #-}
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
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type PropSequentCalc = ClassicalSequentOver PurePropLexicon

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema PropSequentCalc

pattern SeqP x arity      = FX (Lx2 (Lx1 (Predicate x arity)))
pattern SeqSP x arity     = FX (Lx2 (Lx2 (Predicate x arity)))
pattern SeqCon x arity    = FX (Lx2 (Lx3 (Connective x arity)))
pattern SeqProp n         = SeqP (Prop n) AZero
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

instance Combineable PropSequentCalc PropSeqLabel where

    getLabel Top               = PropSeqACUI
    getLabel (_ :+: _)         = PropSeqACUI
    getLabel (GammaV _)        = PropSeqACUI
    --getLabel (SA     _)        = PropSeqACUI
    getLabel _                 = PropSeqFO

    getAlgo PropSeqFO   = foUnifySys
    getAlgo PropSeqACUI = acuiUnifySys

    replaceChild (_ :&-: x)   pig 0 = unEveryPig pig :&-: x
    replaceChild (x :&-: _)   pig 1 = x :&-: unEveryPig pig
    replaceChild (_ :||-: x)  pig 0 = unEveryPig pig :||-: x
    replaceChild (x :||-: _)  pig 1 = x :||-: unEveryPig pig
    replaceChild (_ :->-: x)  pig 0 = unEveryPig pig :->-: x
    replaceChild (x :->-: _)  pig 1 = x :->-: unEveryPig pig
    replaceChild (_ :<->-: x) pig 0 = unEveryPig pig :<->-: x
    replaceChild (x :<->-: _) pig 1 = x :<->-: unEveryPig pig
    replaceChild (_ :+: x)    pig 0 = unEveryPig pig :+: x
    replaceChild (x :+: _)    pig 1 = x :+: unEveryPig pig
    replaceChild (_ :-: x)    pig 0 = unEveryPig pig :-: x
    replaceChild (x :-: _)    pig 1 = x :-: unEveryPig pig
    replaceChild (_ :|-: x)   pig 0 = unEveryPig pig :|-: x
    replaceChild (x :|-: _)   pig 1 = x :|-: unEveryPig pig
    replaceChild (SeqNeg _)   pig _ = SeqNeg $ unEveryPig pig
    replaceChild (SS _ )      pig _ = SS $ unEveryPig pig 
    replaceChild (SA _ )      pig _ = SA $ unEveryPig pig

instance ParsableLex (Form Bool) PurePropLexicon where
        langParser = purePropFormulaParser standardLetters

propSeqParser = seqFormulaParser :: Parsec String u (PropSequentCalc Sequent)

extendedPropSeqParser = parseSeqOver (purePropFormulaParser extendedLetters)

data DerivedRule = DerivedRule { conclusion :: PureForm, premises :: [PureForm]}
               deriving (Show, Eq)

-------------------------
--  1.1 Standard Rules  --
-------------------------
--Rules found in many systems of propositional logic

modusPonens = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
              , GammaV 2 :|-: SS (SeqPhi 1)
              ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)

modusTollens = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
               , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
               ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)

axiom = [] ∴ SA (SeqPhi 1) :|-: SS (SeqPhi 1)

identityRule = [ GammaV 1 :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 1)

doubleNegationElimination = [ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 1) 

doubleNegationIntroduction = [ GammaV 1 :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) 

adjunction = [ GammaV 1  :|-: SS (SeqPhi 1) 
             , GammaV 2  :|-: SS (SeqPhi 2)
             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1 :&-: SeqPhi 2)

conditionalToBiconditional = [ GammaV 1  :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                             , GammaV 2  :|-: SS (SeqPhi 2 :->-: SeqPhi 1) 
                             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)

---------------------------
--  1.1 Variation Rules  --
---------------------------
-- Rules with several variations

modusTollendoPonensVariations = [
                [ GammaV 1  :|-: SS (SeqNeg $ SeqPhi 1) 
                , GammaV 2  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            , 
                [ GammaV 1  :|-: SS (SeqNeg $ SeqPhi 1) 
                , GammaV 2  :|-: SS (SeqPhi 2 :||-: SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ]

constructiveReductioVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,

                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,

                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ]

nonConstructiveReductioVariations = [
                [ GammaV 1 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ,

                [ GammaV 1 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ,

                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( SeqPhi 1)
            ]

conditionalProofVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2) 
            ,   [ GammaV 1 :|-: SS (SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
            ]

simplificationVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :&-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1 :&-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 2)
            ]

additionVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :||-: SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
            ]

biconditionalToConditionalVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :->-: SeqPhi 1)
            , 
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
            ]

proofByCasesVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 3)
                , GammaV 3 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ,   
                [ GammaV 1  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 3)
                , GammaV 3 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ,   
                [ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 3)
                , GammaV 3 :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            , 
                [ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 3)
                , GammaV 3 :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ]

biconditionalProofVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ,
                [ GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ,
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            , 
                [ GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ]

biconditionalPonensVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)
                , GammaV 2  :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)
                , GammaV 2  :|-: SS (SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ]

