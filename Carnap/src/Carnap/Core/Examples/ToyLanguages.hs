{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Examples.ToyLanguages where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Data.Function
import Control.Lens
import Control.Monad.State.Lazy

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

type ToyTerm = ToyLanguage (Term Int)
type ToyForm = ToyLanguage (Form Bool)
                       
--this stuff is kinda boiler plate that I want for the sake of testing
--the user would most likely not care about this stuff
pattern (:!!$:) :: ToyLanguage (a -> b) -> ToyLanguage a -> ToyLanguage b
pattern (:!!$:) f y = f :!$: y
pattern ToyCon x arity = Fx (FRight (FLeft (FLeft (FRight (Connective x arity)))))
pattern ToyPred x arity = Fx (FRight (FLeft (FLeft (FLeft (Predicate x arity)))))
pattern TQuant q = Fx (FRight (FLeft (FRight (Bind q))))
pattern TFunc f arity = Fx (FRight (FRight (Function f arity)))
pattern TVar s = TFunc (Var s) AZero
pattern TAnd = ToyCon And ATwo
pattern TNot = ToyCon Not AOne
pattern TProp n = ToyPred (Prop n) AZero
pattern TAll :: String -> ToyLanguage ((Term Int -> Form Bool) -> Form Bool)
pattern TAll x = TQuant (All x) 
--XXX: TAll appears not to always work in pattern matches
pattern TBind q f = (TQuant q :!!$: LLam f)
--XXX: TBind appears to require :!!$: to resolve some type ambiguities for,
--e.g. show instances.
pattern Conj x y  = TAnd :!$: x :!$: y
pattern (:&:) x y = TAnd :!$: x :!$: y
pattern Neg x = TNot :!$: x
pattern (:=:) x y = ToyPred EqProp (ASucc (ASucc AZero)) :!$: x :!$: y
pattern Univ v f = TBind (All v) f

quantif v f =  (TAll v :!$: LLam f) 

instance Plated (ToyLanguage (Form Bool)) where
        plate f (Conj x y) = Conj <$> f x <*> f y
        plate f (Neg x) = Neg <$> f x
        plate f (Univ v phi) = TBind (All v) <$> abstractTerm (TVar v) 
                                             <$> f (phi $ TVar v)
        plate _ x = pure x
        
--finally you need to tell us how things go togethor
--it is perhaps possible that this will always be the way to do this
instance CopulaSchema ToyLanguage where
    appSchema (TQuant (All x)) (LLam f) e = schematize (All x) (show (f $ TVar x) : e)
    appSchema x y e = schematize x (show y : e)
    lamSchema = error "how did you even do this?"
    liftSchema = error "should not print a lifted value"

instance CanonicalForm ToyForm where
        canonical = relabelVars

instance CanonicalForm ToyTerm where
        canonical = id

--------------------------------------------------------
--1.2 Functions
--------------------------------------------------------

--------------------------------------------------------
--1.2.1 Construction Helpers
--------------------------------------------------------

p0 :: ToyLanguage (Form Bool)
p0 = TProp 0

p1 :: ToyLanguage (Form Bool)
p1 = TProp 1

--------------------------------------------------------
--1.2.2 Instance Helpers
--------------------------------------------------------
--Helper functions for defining instances

--This function lets us base Eq on a canonical formula
relabelVars :: ToyForm -> ToyForm
relabelVars phi = evalState (transformM trans phi) 0
    where trans :: ToyLanguage (Form Bool) -> State Int (ToyLanguage (Form Bool))
          trans (TBind (All _) psi) = do n <- get
                                         put (n+1)
                                         return (TBind (All ("x_" ++ show n)) psi)
          trans x = return x

--This function vacuums a given term out of a formula and returns the
--corresponding function from terms to formulas
abstractTerm :: ToyTerm -> ToyForm -> (ToyTerm -> ToyForm)
abstractTerm v (Conj p p') = \x -> Conj (abstractTerm v p x) (abstractTerm v p' x)
abstractTerm v (Neg p) = \x -> Neg (abstractTerm v p x)
abstractTerm v (TBind q f) = \x -> TBind q ((\g -> g x) . abstractTerm v . f)
abstractTerm v (v' :=: v'') = \x -> (if v == v' then x else v') :=: (if v == v'' then x else v'')
abstractTerm _ p = const p

--------------------------------------------------------
--2. A Simply Typed Lambda Calculus
--------------------------------------------------------
--TODO: I think it'd be best to split this into a separate file to avoid
--e.g. very crazy symbols for our specializations of :!$:

data Application c where
        App :: Application (Term (a -> b) -> Term a -> Term b)

data IntObject a where
        IntOb :: Int -> IntObject (Term Int)

data Abstraction c where
        Abs :: Abstraction ((Term a -> Term b) -> Term (a -> b))

type SimpleLambda = FixLang (Abstractors Abstraction
                          :|: Function IntObject
                          :|: Applicators Application)

pattern (:!$$:) :: SimpleLambda (a -> b) -> SimpleLambda a -> SimpleLambda b
pattern (:!$$:) f y = f :!$: y
pattern ObFunc f arity = Fx (FRight (FLeft (FRight (Function f arity))))
pattern AppFunc f = Fx (FRight (FRight ((Apply f))))
pattern SAbstract q = Fx (FRight (FLeft (FLeft (Abstract q))))
pattern SimpAbs f = (SAbstract Abs) :!$$: LLam f
pattern SimpInt n = ObFunc (IntOb n) AZero
pattern SimpApp a b = (AppFunc App) :!$$: a :!$$: b
