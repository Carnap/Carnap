{-#LANGUAGE FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Unification (
   Equation((:=:)), FirstOrder, HigherOrder,
   isVar, sameHead, decompose, occurs, subst,
   matchApp, castLam, getLamVar, (.$.),
   applySub, founify, mapAll 
) where

import Data.Type.Equality
import Data.Typeable
import Carnap.Core.Data.AbstractSyntaxClasses (Schematizable(..))

data Equation f where
    (:=:) :: f a -> f a -> Equation f

instance Schematizable f => Show (Equation f) where
        show (x :=: y) = schematize x [] ++ " :=: " ++ schematize y []

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

data ExtApp f a where
    ExtApp :: f (b -> a) -> f b -> ExtApp f a

class FirstOrder f => HigherOrder f where
    matchApp :: f a -> Maybe (ExtApp f a)
    castLam :: f a -> Maybe (f (b -> c), a :~: (b -> c))
    getLamVar :: f (a -> b) -> f a
    (.$.) :: f (a -> b) -> f a -> f b

data UError f where
    SubError :: f a -> f a -> UError f -> UError f
    MatchError ::  f a -> f a -> UError f
    OccursError :: f a -> f a -> UError f

instance Schematizable f => Show (UError f) where
        show (SubError x y e) =  show e ++ "with suberror"
                                 ++ schematize x [] ++ ", " 
                                 ++ schematize y []
        show (MatchError x y) = "Match Error:"
                                 ++ schematize x [] ++ ", " 
                                 ++ schematize y []
        show (OccursError x y) = "OccursError: " 
                                 ++ schematize x [] ++ ", " 
                                 ++ schematize y []

emap :: (forall a. f a -> f a) -> Equation f -> Equation f
emap f (x :=: y) = f x :=: f y

mapAll :: (forall a. f a -> f a) -> [Equation f] -> [Equation f]
mapAll f = map (emap f)

(Left x) .<. f = Left (f x)
x .<. _ = x

founify :: FirstOrder f => [Equation f] -> [Equation f] -> Either (UError f) [Equation f]
founify [] ss = Right ss
founify ((x :=: y):es) ss
    | isVar x && occurs x y       = Left $ OccursError x y
    | isVar x && not (occurs x y) = founify (mapAll (subst x y) es) ((x :=: y):ss)
    | isVar y                     = founify ((y :=: x):es) ss
    | sameHead x y                = founify (es ++ decompose x y) ss .<. SubError x y
    | otherwise                   = Left $ MatchError x y

applySub :: FirstOrder f => [Equation f] -> f a -> f a
applySub []             y = y
applySub ((v :=: x):ss) y = applySub ss (subst v x y)
