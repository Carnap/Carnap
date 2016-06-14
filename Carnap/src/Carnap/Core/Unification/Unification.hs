{-#LANGUAGE ImpredicativeTypes, FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Unification (
   Equation((:=:)), FirstOrder, HigherOrder,
   isVar, sameHead, decompose, occurs, subst,
   matchApp, castLam, getLamVar, (.$.),
   applySub, mapAll, freshVars,
   EveryPig(EveryPig), unEveryPig, ExtApp(ExtApp),
   AnyPig(AnyPig), freeVars
) where

import Data.Type.Equality
import Carnap.Core.Util
import Data.Typeable

data Equation f where
    (:=:) :: (Typeable a, FirstOrder f) => f a -> f a -> Equation f

--this interface seems simpliar for the user to implement than our previous
--1. There is no more varible type
--2. There is no substitution type
--3. other than decompose the operations are simpliar. For instance rather than
--   freeVars there is occurs. rather than a full substitution there is just
--   a single varible substitution. rather than combining sameHead and decompose
--   they are seperate methods. rather than converting a varible to check if it
--   it is a varible we just have 'isVar'
--4. Addtionally I have tried to allow this to meet the demands of more
--   unification algorithms so that this is a one stop shop for unification
--5. I have tried to name things here in a way that someone reading the HoAR
--   would recognize (hence "decompose" rather than "match")
class FirstOrder f where
    isVar :: f a -> Bool
    sameHead :: f a -> f a -> Bool
    decompose :: f a -> f a -> [Equation f]
    occurs :: f a -> f b -> Bool
    subst :: f a -> f a -> f b -> f b
    freshVars :: [EveryPig f] --we need to universially quantify this

data ExtApp f a where
    ExtApp :: f (b -> a) -> f b -> ExtApp f a

class FirstOrder f => HigherOrder f where
    matchApp :: f a -> Maybe (ExtApp f a)
    castLam :: f a -> Maybe (f (b -> c), a :~: (b -> c))
    getLamVar :: f (a -> b) -> f a
    (.$.) :: f (a -> b) -> f a -> f b

data UError f where
    SubError :: FirstOrder f => f a -> f a -> UError f -> UError f
    MatchError :: FirstOrder f => f a -> f a -> UError f
    OccursError :: FirstOrder f => f a -> f a -> UError f

emap :: (forall a. f a -> f a) -> Equation f -> Equation f
emap f (x :=: y) = f x :=: f y

mapAll :: (forall a. f a -> f a) -> [Equation f] -> [Equation f]
mapAll f = map (emap f)

(Left x) .<. f = Left (f x)
x .<. _ = x

applySub :: FirstOrder f => [Equation f] -> f a -> f a
applySub []             y = y
applySub ((v :=: x):ss) y = applySub ss (subst v x y)

freeVars :: (Typeable a, FirstOrder f) => f a -> [AnyPig f]
freeVars t | isVar t   = [AnyPig t]
           | otherwise = concatMap rec (decompose t t)
    where rec (a :=: _) = freeVars a
