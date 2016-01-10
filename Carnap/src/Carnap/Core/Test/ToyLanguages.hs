{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Test.ToyLanguages where 

import Carnap.Core.Data.AbstractSyntaxDataTypes

--This module gives some toy language examples, with instances of
--important typeclasses, and explanation of the guiding ideas behind them.
--These are not meant for use, but to be used as templates for manually, or
--eventually, programatically, generating other languages with similar
--features.

--------------------------------------------------------
--1. Type one languages
--------------------------------------------------------

--these are languages in which the saturated linguistic items are always of
--the form `lang a (Form b)` or `lang a (Term b)`
--
--Constructors for semantic categories like ToyPredicate a, ToyConnective
--a, fed into Predicate and Connective constructors give rise to
--unsaturated linguistic items that can be combined with other (saturated
--or unsaturated) linguistic items via application.
--
--Evaluation and satisfaction are computed for saturated linguistic items
--by decomposing these into the different constructors for the semantic
--categories involved, evaluating those constructors, and applying them 

--------------------------------------------------------
--1.1 Data Types
--------------------------------------------------------

--A semantic category consisting of infinitely many simple true-or-false propositions. 
data BasicProp a where
        Prop :: Int -> BasicProp Bool

instance Schematizable BasicProp where
        schematize (Prop n) = \_ -> "P_" ++ show n

instance Evaluable BasicProp where
        eval (Prop n) = even n

instance Modelable (Int -> Bool) BasicProp where
        satisfies f (Prop n) = f n

--A semantic category consisting of boolean conjunction and negation
data BasicConn a where
        And :: BasicConn (Bool -> Bool -> Bool)
        Not :: BasicConn (Bool -> Bool)

instance Schematizable BasicConn where
        schematize And = \(x:y:_) -> "(" ++ x ++ " ∧ " ++ y ++ ")"
        schematize Not = \(x:_) -> "¬" ++ x 

instance Evaluable BasicConn where
        eval And = (&&)
        eval Not = not

instance Modelable (Int -> Bool) BasicConn where
        satisfies f And = (&&)
        satisfies f Not = not

type ToyLanguage lang a = ((Copula :|: (Predicate BasicProp :|: Connective BasicConn )) lang a)

pattern ToyCon x arity = Mix1 (Mix1 (Connective x arity))

pattern ToyPred x arity = Mix1 (Mix0 (Predicate x arity))

pattern ToyLam x  = Mix0 (Lam x)

pattern x :!$: y = Mix0 (x :$: y)
                            
toyConjunction :: ToyLanguage a (Form Bool -> Form Bool -> Form Bool)
toyConjunction = ToyCon And (FASucc (FASucc FAZero))

toyNegation :: ToyLanguage a (Form Bool -> Form Bool)
toyNegation = ToyCon Not (FASucc FAZero)

toyProp :: Int -> ToyLanguage a (Form Bool)
toyProp n = ToyPred (Prop n) FAZero

--------------------------------------------------------
--1.2 Semantic Instances
--------------------------------------------------------
--these can be written parametrically, without any information about the
--semantic categories of the language, other than the fact that objects in
--those categories are evaluable

instance (Evaluable con, Evaluable pred) => 
        LEvaluable (Copula :|: (Predicate pred :|: Connective con)) Form where
        leval (ToyPred p FAZero) = eval p
        leval (ToyCon c (FASucc FAZero) :!$: t) = eval c $ leval t
        leval (ToyCon c (FASucc (FASucc FAZero)) :!$: t :!$: t') = eval c (leval t) (leval t')
        leval (ToyLam f :!$: t) = leval (f t)

instance (Modelable (Int -> Bool) con, Modelable (Int -> Bool) pred) => 
        LModelable (Int -> Bool) (Copula :|: (Predicate pred :|: Connective con)) Form where
        lsatisfies m (ToyPred p FAZero) = satisfies m p
        lsatisfies m (ToyCon c (FASucc FAZero) :!$: t) = satisfies m c $ lsatisfies m t
        lsatisfies m (ToyCon c (FASucc (FASucc FAZero)) :!$: t :!$: t') = satisfies m c (lsatisfies m t) (lsatisfies m t')
        lsatisfies m (ToyLam f :!$: t) = lsatisfies m (f t)

instance (Schematizable con, Schematizable pred) =>
        LSchematizable (Copula :|: (Predicate pred :|: Connective con)) where
        lschematize (ToyPred p FAZero) = schematize p
        lschematize (ToyCon c (FASucc FAZero) :!$: t) = \y -> schematize c [lschematize t y]
        lschematize (ToyCon c (FASucc (FASucc FAZero)) :!$: t :!$: t') = \y -> schematize c [lschematize t y, lschematize t' y]
        lschematize (ToyLam f :!$: t) = lschematize (f t)
