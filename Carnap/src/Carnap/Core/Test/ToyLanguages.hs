{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Test.ToyLanguages where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Data.Function

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
        Prop :: Int -> BasicProp (Form Bool)
        EqProp :: BasicProp (Term Int -> Term Int -> Form Bool)

instance Schematizable BasicProp where
        schematize (Prop n)   _       = "P_" ++ show n
        schematize EqProp     (x:y:_) = x ++ " = " ++ y

instance Evaluable BasicProp where
        eval (Prop n) = Form $ even n
        eval EqProp   = \(Term t) (Term t') -> Form $ t == t'

instance Modelable ([Int], Int -> Bool) BasicProp where
        satisfies (s, f) (Prop n) = Form $ f n
        satisfies (s, f) EqProp = eval EqProp

--A semantic category consisting of boolean conjunction and negation
data BasicConn a where
        And :: BasicConn (Form Bool -> Form Bool -> Form Bool)
        Not :: BasicConn (Form Bool -> Form Bool)

instance Schematizable BasicConn where
        schematize And = \(x:y:_) -> "(" ++ x ++ " ∧ " ++ y ++ ")"
        schematize Not = \(x:_) -> "¬" ++ x

instance Evaluable BasicConn where
        eval And = lift2 (&&)
        eval Not = lift1 not

instance Modelable ([Int], Int -> Bool) BasicConn where
    satisfies _ x = eval x

data BasicQuant a where
        All :: String -> BasicQuant ((Term Int -> Form Bool) -> Form Bool)

instance Schematizable BasicQuant where
        schematize (All v) = \(x:_) -> "∀" ++ v ++ "(" ++ x ++ ")"

instance Evaluable BasicQuant where
        eval (All _) = \f -> Form $ all (eval . f) (map Term [0..1000])

instance Modelable ([Int], Int -> Bool) BasicQuant where
        satisfies (s, m) (All _) = \f -> Form $ all (eval . f) (map Term s)

data BasicTerm a where
    Var :: String -> BasicTerm (Term Int)

instance Schematizable BasicTerm where
    schematize (Var x) _ = x

instance Evaluable BasicTerm where
    eval = error "only closed terms are evaluable"

instance Modelable ([Int], Int -> Bool) BasicTerm where
    satisfies = error "only closed terms are modelable"

--mix in your parts using :|: and fix the language with FixLang
--assign a name "ToyLanguage" to this type
--this type can then be indexed with their semantic type
type ToyLanguage = FixLang (Predicate BasicProp
                       :|: Connective BasicConn
                       :|: Quantifiers BasicQuant
                       :|: Function BasicTerm)

--this stuff is kinda boiler plate that I want for the sake of testing
--the user would most likely not care about this stuff
pattern ToyCon x arity = Fx (FRight (FLeft (FLeft (FRight (Connective x arity)))))
pattern ToyPred x arity = Fx (FRight (FLeft (FLeft (FLeft (Predicate x arity)))))
pattern TQuant q = Fx (FRight (FLeft (FRight (Bind q))))
pattern TFunc f arity = Fx (FRight (FRight (Function f arity)))
pattern TVar s = TFunc (Var s) AZero
pattern TAnd = ToyCon And (ASucc (ASucc AZero))
pattern TNeg = ToyCon Not (ASucc AZero)
pattern TProp n = ToyPred (Prop n) AZero
pattern TLam f = Fx (FLeft (Lam f))
--pattern TAll x =  TQuant (All x)
pattern (:!$:) f x = Fx (FLeft (f :$: x))
pattern (:=:) x y = ToyPred EqProp (ASucc (ASucc AZero)) :!$: x :!$: y

alle :: String -> (ToyLanguage (Term Int) -> ToyLanguage (Form Bool)) -> ToyLanguage (Form Bool)
alle x f = TQuant (All x) :!$: TLam f
(.&.) :: ToyLanguage (Form Bool) -> ToyLanguage (Form Bool) -> ToyLanguage (Form Bool)
x .&. y = TAnd :!$: x :!$: y
p0 :: ToyLanguage (Form Bool)
p0 = TProp 0
p1 :: ToyLanguage (Form Bool)
p1 = TProp 1

neg :: ToyLanguage (Form Bool) -> ToyLanguage (Form Bool)
neg x = TNeg :!$: x

--finally you need to tell us how things go togethor
--it is perhaps possible that this will always be the way to do this
instance CopulaSchema ToyLanguage where
    appSchema (TQuant (All x)) (TLam f) e = schematize (All x) (show (f $ TVar x) : e)
    appSchema x y e = schematize x (show y : e)
    lamSchema = error "how did you even do this?"
    liftSchema = error "should not print a lifted value"
