{-#LANGUAGE TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Data.AbstractSyntaxDataTypes(
  Modelable, Evaluable,
  satisfies, eval, schematize,
  Copula((:$:), Lam), (:|:)(FLeft, FRight), Quantifiers(Bind),
  Nat(Zero, Succ), Fix(Fx), Vec(VNil, VCons), Arity(AZero, ASucc),
  Predicate(Predicate), Connective(Connective), Function(Function),
  Subnective(Subnective),
  Schematizable, FixLang --, LLam, (:!$:)
) where

import Carnap.Core.Util

--This module attempts to provide abstract syntax types that would cover
--a wide variety of languages

--------------------------------------------------------
--1. Abstract typeclasses
--------------------------------------------------------

--class of terms that we can compute a fregean denotation for, relative to
--a model or assignment of some sort.
-- | a type is modelable if it can be modeled. these are generally parts from
-- | which LModelable types are built up
class Modelable m f where
        satisfies :: m -> f a -> a

-- | Just like modelable but where a default model is picked for us
-- | this is useful as a convience and when there is one cononical model
-- | such as in the case of peano arithmetic
class Evaluable f where
        eval :: f a -> a


class Liftable f where
        lift :: a -> f a

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

-- | this is the type that describes how things are connected
-- | Things are connected either by application or by
-- | a lambda abstraction. The 'lang' parameter gets fixed to
-- | form a fully usable type
--
-- @
--    Fix (Copula :|: Copula :|: (Predicate BasicProp :|: Connective BasicConn))
-- @
data Copula lang t where
    (:$:) :: lang (t -> t') -> lang t -> Copula lang t'
    Lam :: (lang t -> lang t') -> Copula lang (t -> t')
    Lift :: t -> Copula lang t

-- | this is type acts a disjoint sum/union of two functors
-- | it carries though the phantom type as well
data (:|:) :: (k -> k' -> *) -> (k -> k' -> *) -> k -> k' -> * where
    FLeft :: f x idx -> (f :|: g) x idx
    FRight :: g x idx -> (f :|: g) x idx

-- | This type fixes the first argument of a functor and carries though a
-- | phantom type
-- | note that only certian kinds of functors even have a kind
-- | such that the first argument is fixable
newtype Fix f idx = Fx (f (Fix f) idx)

type FixLang f = Fix (Copula :|: f)

data Quantifiers :: (* -> *) -> (* -> *) -> * -> * where
    Bind :: quant ((t a -> f b) -> f b) -> Quantifiers quant lang ((t a -> f b) -> f b)

-- | think of this as a type constraint. the lang type, model type, and number
-- | must all match up for this type to be inhabited
-- | this lets us do neat type safty things
data Arity :: * -> * -> Nat -> * -> * where
    AZero :: Arity arg ret Zero ret
    ASucc :: Arity arg ret n ret' -> Arity arg ret (Succ n) (arg -> ret')

data Predicate :: (* -> *) -> (* -> *) -> * -> * where
    Predicate :: pred t -> Arity a b n t -> Predicate pred lang t

data Connective :: (* -> *) -> (* -> *) -> * -> * where
    Connective :: con t -> Arity a b n t -> Connective con lang t

data Function :: (* -> *) -> (* -> *) -> * -> * where
    Function :: func t -> Arity a b n t -> Function func lang t

data Subnective :: (* -> *) -> (* -> *) -> * -> * where
    Subnective :: sub t -> Arity a b n t -> Subnective sub lang t

--------------------------------------------------------
--3. Schematizable, Show, and Eq
--------------------------------------------------------


class Schematizable f where
        schematize :: f a -> [String] -> String

{--
instance -# OVERLAPPABLE #- (Schematizable (f a), Schematizable (g a)) => Schematizable ((f :|: g) a) where
        schematize (FLeft a) = schematize a
        schematize (FRight a) = schematize a

instance Schematizable (f (Fix f)) => Schematizable (Fix f) where
    schematize (Fx a) = schematize a

pattern LLam x  = Fx (FLeft (Lam x))
pattern x :!$: y = Fx (FLeft (x :$: y))

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

instance -# OVERLAPPABLE #- (Schematizable (f a), Schematizable (g a)) => Show ((f :|: g) a b) where
        show (FLeft a) = schematize a []
        show (FRight a) = schematize a []

instance Schematizable (f (Fix f)) => Show (Fix f idx) where
        show (Fx a) = schematize a []

instance -# OVERLAPPING #- Schematizable ((Copula :|: f1) a) => Show ((Copula :|: f1) a b) where
        show a = schematize a []

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

instance -# OVERLAPPABLE #- (Schematizable (f a), Schematizable (g a)) => Eq ((f :|: g) a b) where
        x == y = show x == show y

instance (Schematizable (f (Fix f))) => Eq (Fix f idx) where
        x == y = show x == show y

instance -# OVERLAPPING #- Schematizable ((Copula :|: f1) a) => Eq ((Copula :|: f1) a b) where
        x == y = show x == show y

--I don't *think* I need this, not really sure
--instance LSchematizable (Copula :|: lang) => Eq (Copula ((Copula :|: lang) a) b) where
        --x == y = show x == show y

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
--}
--------------------------------------------------------
--4. Evaluation and Modelable
--------------------------------------------------------

instance Evaluable quant => Evaluable (Quantifiers quant lang) where
    eval (Bind q) = eval q

instance Evaluable pred => Evaluable (Predicate pred lang) where
    eval (Predicate p a) = eval p

instance Evaluable con => Evaluable (Connective con lang) where
    eval (Connective p a) = eval p

instance Evaluable func => Evaluable (Function func lang) where
    eval (Function p a) = eval p

instance Evaluable sub => Evaluable (Subnective sub lang) where
    eval (Subnective p a) = eval p

instance (Evaluable (f lang), Evaluable (g lang)) => Evaluable ((f :|: g) lang) where
    eval (FLeft p) = eval p
    eval (FRight p) = eval p

instance (Evaluable (f (Fix f))) => Evaluable (Fix f) where
    eval (Fx a) = eval a

instance Liftable (Fix (Copula :|: a)) where
    lift a = Fx $ FLeft (Lift a)

instance (Liftable lang, Evaluable lang) => Evaluable (Copula lang) where
    eval (f :$: x) = eval f (eval x)
    eval (Lam f) = \t -> eval $ f (lift t)
    eval (Lift t) = t

instance Modelable m quant => Modelable m (Quantifiers quant lang) where
    satisfies m (Bind q) = satisfies m q

instance Modelable m pred => Modelable  m (Predicate pred lang) where
    satisfies m (Predicate p a) = satisfies m p

instance Modelable m con => Modelable m (Connective con lang) where
    satisfies m (Connective p a) = satisfies m p

instance Modelable m func => Modelable m (Function func lang) where
    satisfies m (Function p a) = satisfies m p

instance Modelable m sub => Modelable m (Subnective sub lang) where
    satisfies m (Subnective p a) = satisfies m p

instance (Modelable m (f lang), Modelable m (g lang)) => Modelable m ((f :|: g) lang) where
    satisfies m (FLeft p) = satisfies m p
    satisfies m (FRight p) = satisfies m p

instance (Modelable m (f (Fix f))) => Modelable m (Fix f) where
    satisfies m (Fx a) = satisfies m a

instance (Liftable lang, Modelable m lang) => Modelable m (Copula lang) where
    satisfies m (f :$: x) = satisfies m f (satisfies m x)
    satisfies m (Lam f) = \t -> satisfies m $ f (lift t)
    satisfies m (Lift t) = t
