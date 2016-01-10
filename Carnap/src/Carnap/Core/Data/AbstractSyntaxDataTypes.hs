{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, IncoherentInstances, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Data.AbstractSyntaxDataTypes where 

--This module attempts to provide abstract syntax types that would cover
--a wide variety of languages

--------------------------------------------------------
--1. Abstract typeclasses
--------------------------------------------------------

--class of terms that we can compute a fregean denotation for, relative to
--a model or assignment of some sort.

class LModelable m lang f where
        lsatisfies :: m -> lang a (f b) -> b

class Modelable m f where
        satisfies :: m -> f a -> a

class Evaluable f where
        eval :: f a -> a 

class LEvaluable lang f where
        leval :: lang a (f b) -> b

class PForm lang f where
        mainC :: lang a (f b) -> c

--------------------------------------------------------
--2. Abstract Types
--------------------------------------------------------

--Here are some types for abstract syntax. The basic proposal
--is that we only define how terms of different types connect
--and let the user define all the connections independently of
--of their subparts. In some sense they just define the type
--and the type system figures out how they can go together

--We use the idea of a semantic value to indicate approximately a Fregean
--sense, or intension: approximately a function from models to Fregean
--denotations in those models

--------------------------------------------------------
--2.1 Abstract Terms
--------------------------------------------------------

--the type that indicates a term in a phantom type
data Term a
--the type that indicates a formula in a phantom type
data Form a

--this is the type that describes how things are connected
--Things are connected either by application or by
--a lambda abstraction. The 'lang' parameter gets fixed to 
--form a fully usable type
data Copula lang t where
    (:$:) :: lang (t -> t') -> lang t -> Copula lang t'
    Lam :: (lang t -> lang t') -> Copula lang (t -> t')

--this is the type that glues everything together by fixing a parameter
--of the functor. This allows types defined in separate systems to be
--marbled together into a single type as if by mutual recursion 
data (:|:) :: ((k -> *) -> k -> *) -> ((k -> *) -> k -> *) -> (k -> *) -> k -> * where
    Mix0 :: f0 ((f0 :|: f1) a) idx -> (f0 :|: f1) a idx
    Mix1 :: f1 ((f0 :|: f1) a) idx -> (f0 :|: f1) a idx
    Unmix :: a idx -> (f0 :|: f1) a idx

--this is just my best current guess. This is very open to discussion
data Quantifiers :: (* -> *) -> (* -> *) -> * -> * where
    Bind :: quant ((t a -> f b) -> f b) -> Quantifiers quant lang ((t a -> f b) -> f b)

--define natural numbers for type lifting
data Nat = Zero
         | Succ Nat

--think of this as a type constraint.
--Arity arg ret N T holds only if T takes N arguments of type 'arg' and returns a 'ret'
data Arity :: * -> * -> Nat -> * -> * where
    AZero :: Arity arg ret (Succ Zero) ret
    ASucc :: Arity arg ret n ret' -> Arity arg ret (Succ n) (arg -> ret')

data FArity :: (* -> *) -> * -> ( * -> *) -> * -> Nat -> * -> * -> * where
    FAZero :: FArity f arg g ret (Succ Zero) ret (g ret)
    FASucc :: FArity f arg g ret n ret' fret' -> FArity f arg g ret (Succ n) (arg -> ret') (f arg -> fret') 

--all these "Functors" are very open to interpretation. I could be missing needed information here

data Predicate :: (* -> *) -> (* -> *) -> * -> * where
    Predicate :: pred t -> FArity Term a Form b n t t' -> Predicate pred lang t'

data Connective :: (* -> *) -> (* -> *) -> * -> * where
    Connective :: con t -> FArity Form a Form b n t t' -> Connective con lang t'

data Function :: (* -> *) -> (* -> *) -> * -> * where
    Function :: func t -> FArity Term a Term b n t t' -> Function func lang t'

data Subnective :: (* -> *) -> (* -> *) -> * -> * where
    Subnective :: sub t -> FArity Form a Term b n t t' -> Subnective sub lang t'

--------------------------------------------------------
--3. Schematizable, Show, and Eq
--------------------------------------------------------

class Schematizable f where
        schematize :: f a -> [String] -> String

class LSchematizable lang where
        lschematize :: lang a b -> [String] -> String

instance (Schematizable (f0 ((f0 :|: f1) a)), 
          Schematizable (f1 ((f0 :|: f1) a))) => Schematizable ((f0 :|: f1) a) where
        schematize (Mix0 a) = schematize a
        schematize (Mix1 a) = schematize a
        schematize (Unmix a) = undefined 
        --couldn't figure out how to assign this. The trouble is that a is
        --polymorphic, at least in the toy languages constructed so far. If
        --there's a way of making languages without that feature, then we
        --could add Schematizable a as a constraint, and allow for Unmixing

instance LSchematizable (Copula :|: lang) => Schematizable ((Copula :|: lang) a) where
         schematize = lschematize

--XXX: I have no clue how to do this right now
--the issue is that we don't actully have the whole term/formula here
--so we can't really come up with a quantifier
instance Schematizable quant => Schematizable (Quantifiers quant lang) where
        schematize (Bind q) arg = schematize q arg --here I assume 'q' stores the users varible name

instance Schematizable pred => Schematizable (Predicate pred lang) where
        schematize (Predicate p _) = schematize p

instance Schematizable con => Schematizable (Connective con lang) where
        schematize (Connective c _) = schematize c

instance Schematizable func => Schematizable (Function func lang) where
        schematize (Function f _) = schematize f

instance Schematizable sub => Schematizable (Subnective sub lang) where
        schematize (Subnective s _) = schematize s

instance (Schematizable (f0 ((f0 :|: f1) a)), 
          Schematizable (f1 ((f0 :|: f1) a))) => Show ((f0 :|: f1) a b) where
        show (Mix0 a) = schematize a []
        show (Mix1 a) = schematize a []

instance (Show (Copula ((Copula :|: f1) a) b), 
          Schematizable (f1 ((Copula :|: f1) a))) => Show ((Copula :|: f1) a b) where
        show (Mix0 a) = show a
        show (Mix1 a) = schematize a []

instance LSchematizable (Copula :|: lang) => Show (Copula ((Copula :|: lang) a) b) where
         show x = lschematize (Mix0 x) [] 

instance Schematizable quant => Show (Quantifiers quant lang a) where
        show x = schematize x []

instance Schematizable pred => Show (Predicate pred lang a) where
        show x = schematize x []

instance Schematizable con => Show (Connective con lang a) where
        show x = schematize x []

instance Schematizable func => Show (Function func lang a) where
        show x = schematize x []

instance Schematizable sub => Show (Subnective sub lang a) where
        show x = schematize x []

instance (Schematizable (f0 ((f0 :|: f1) a)), 
          Schematizable (f1 ((f0 :|: f1) a))) => Eq ((f0 :|: f1) a b) where
        x == y = show x == show y

instance (Show (Copula ((Copula :|: f1) a) b), 
          Schematizable (f1 ((Copula :|: f1) a))) => Eq ((Copula :|: f1) a b) where
        x == y = show x == show y

instance LSchematizable (Copula :|: lang) => Eq (Copula ((Copula :|: lang) a) b) where
        x == y = show x == show y

instance Schematizable quant => Eq (Quantifiers quant lang a) where
        x == y = show x == show y

instance Schematizable pred => Eq (Predicate pred lang a) where
        x == y = show x == show y

instance Schematizable con => Eq (Connective con lang a) where
        x == y = show x == show y

instance Schematizable func => Eq (Function func lang a) where
        x == y = show x == show y

instance Schematizable sub => Eq (Subnective sub lang a) where
        x == y = show x == show y
