{-#LANGUAGE RankNTypes,TypeOperators, ScopedTypeVariables, GADTs, MultiParamTypeClasses #-}

module Carnap.Core.Data.Util (equalizeTypes, incArity, checkChildren,
mapover, (:~:)(Refl)) where

--this module defines utility functions and typeclasses for manipulating
--the data types defined in Core.Data

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Data.Typeable
import Control.Lens.Plated (Plated, cosmos, transform, children)
import Control.Lens.Fold (anyOf)
import Data.Typeable

--------------------------------------------------------
--1.Utility Functions
--------------------------------------------------------

equalizeTypes :: FixLang f a -> FixLang f b -> Maybe (a :~: b)
equalizeTypes (x@(Fx _) :: FixLang f a) (y@(Fx _) :: FixLang f b) = eqT :: Maybe (a :~: b)
equalizeTypes _ _ = Nothing

{-|
This function replaces the head of a given language item with another head
that increases the arity of the item.
-}
incArity :: (Typeable a, Typeable b) => 
    (forall c . FixLang l c ->  Maybe (FixLang l (b -> c))) -> 
    FixLang l (b -> a)  ->  Maybe (FixLang l (b -> b -> a))
incArity f ((head :: FixLang l (t -> b -> a)) :!$: (tail :: FixLang l t)) = 
        case eqT :: Maybe (t :~: b) of
            Nothing -> Nothing
            Just Refl ->  do x <- incArity f head
                             return $ x :!$: tail
incArity f head = f head

{-|
this function checks to see if phi occurs as a child of psi
-}
checkChildren :: (Eq s, Plated s) => s -> s -> Bool
checkChildren phi psi = phi /= psi && anyOf cosmos (== phi) psi

{-|
this function will, given a suitably polymorphic argument `f`, apply `f` to each of the children of the linguistic expression `le`.
-}
mapover :: (forall a . FixLang l a -> FixLang l a) -> FixLang l b -> FixLang l b
mapover f le@(x :!$: y) = mapover f x :!$: f y
mapover f x = x
