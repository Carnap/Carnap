{-#LANGUAGE TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, ScopedTypeVariables, AutoDeriveTypeable, DefaultSignatures #-}
module Carnap.Core.Data.AbstractSyntaxClasses
    where

--------------------------------------------------------
--1. Abstract typeclasses
--------------------------------------------------------

{-|
Evaluable data  can be assigned a semantic value.  In the case of a formula
(e.g. `2 + 2 = 4 :: Arithmetic (Form True)`)---an this might be for
example, a truth value (in this case, `True`). In the case of a term, (e.g.
`2 + 2 :: Arithmetic (Term Int)`), this might be for, example, an integer
(in this case, `4`)
-}
class Evaluable f where
    eval :: f a -> a

{-|   
Modelable data can be assigned a semantic value, but only relative to
a model---for example, in propositional logic `P_1 ∧ P_2 ::
PropositionalLogic (Form True)` has a truth value relative to an assignment
of truth values to truth values (which can be represented by a function
`Int -> Bool`
-}
class Modelable m f where
    satisfies :: m -> f a -> a

class Liftable f where
    lift :: a -> f a

lift1 :: (Evaluable f, Liftable f) => (a -> b) -> (f a -> f b)
lift1 f = lift . f . eval

lift2 :: (Evaluable f, Liftable f) => (a -> b -> c) -> (f a -> f b -> f c)
lift2 f fa fb = lift (f (eval fa) (eval fb))

{-|
Schematizable data are associated with a way to take a list of strings
associated with other data and bind them together to produce a new
string representing the original datum combined with the other data. for
example, the plus symbol might be schematized by a function `\(x:y:zs) ->
x ++ " + " ++ y`. That means that when symbol is combined with
some other data, say, the numerals 1 and 2, then the result will be
represented by "1 + 2"
-}
class Schematizable f where
    schematize :: f a -> [String] -> String

class UniformlyEq f where
        (=*) :: f a -> f b -> Bool


{-|
CanonicalForm is a typeclass for data which can be put in a canonical form.
For example, the canonical form of sentence of quantified logic might be
a formula in which the variables are labeled sequentially. 
-}
class CanonicalForm a where
    canonical :: a -> a
    canonical = id


