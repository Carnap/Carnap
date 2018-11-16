{-#LANGUAGE ImpredicativeTypes, FlexibleContexts, RankNTypes,TypeOperators, ScopedTypeVariables, GADTs, MultiParamTypeClasses #-}

module Carnap.Core.Data.Util (scopeHeight, equalizeTypes, incArity, checkChildren,
mapover, (:~:)(Refl), Buds(..), Blossoms(..), bloom, sbloom, grow, rebuild, castToProxy, castTo) where

--this module defines utility functions and typeclasses for manipulating
--the data types defined in Core.Data

import Carnap.Core.Util
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification
import Data.Typeable
import Data.List (nub)
import Control.Lens.Plated (Plated, cosmos, transform, children)
import Control.Lens.Fold (anyOf)
import Control.Monad.State.Lazy as S

--------------------------------------------------------
--1.Utility Functions
--------------------------------------------------------

{-|
Given two occupants of a typed fixpoint, this function returns @Just@
a proof of the equality of their types, if their types are equal, and
otherwise @Nothing@.  Concretely, it lets you do things like dispatch to
different behaviors depending on the type of your arguments, for all the
languages that Carnap supports (since these languages are typed
fixedpoints).

For example, suppose you have two functions @f :: Language Int -> Bool@ and
@g :: Language Bool -> Bool@, and two representative language items @a ::
Language Int@, and @b :: Language Bool@. Then you can write

> combine f g v = case equalizeTypes v a of
>                     Just Refl -> f v
>                     Nothing -> case equalizeTypes v b of
>                         Just Refl -> g v
>                         Nothing -> False

to union the functions into a single polymorphic function.

-}
equalizeTypes :: Fix f a -> Fix f b -> Maybe (a :~: b)
equalizeTypes (x@(Fx _) :: Fix f a) (y@(Fx _) :: Fix f b) = eqT :: Maybe (a :~: b)

castToProxy :: Typeable a => Proxy a -> Fix f b -> Maybe (a :~: b)
castToProxy (Proxy :: Proxy a) (y@(Fx _) :: Fix f b) = eqT :: Maybe (a :~: b)

castTo :: forall a b f. (Typeable a, Typeable b) => Fix f b -> Maybe (Fix f a)
castTo x = case eqT :: Maybe (a :~: b) of Nothing -> Nothing; Just Refl -> Just x

{-|
This function replaces the head of a given language item with another head
that increases the arity of the item.
-}
incArity :: (Typeable a, Typeable b) => 
    (forall c. Typeable c => FixLang l c ->  Maybe (FixLang l (b -> c))) -> 
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
this function will, given a suitably polymorphic argument `f`, apply `f` to each of the immediate children of the linguistic expression `le`.
-}
mapover :: (forall a. FixLang l a -> FixLang l a) -> FixLang l b -> FixLang l b
mapover f le@(x :!$: y) = mapover f x :!$: f y
mapover f x = x

{-|
This function will assign a height to a given linguistic expression,
greater than the height of any of any formula in the scope of one of its
variable-binding subexpressions
-}
scopeHeight :: MonadVar (FixLang f) (State Int) => FixLang f a -> Int
scopeHeight (x :!$: y) = max (scopeHeight x) (scopeHeight y)
scopeHeight (LLam f) = scopeHeight (f dv) + 1
    where  dv = evalState fresh (0 :: Int)
scopeHeight _ = 0

{-|
This function will rebuild a given linguistic expression, removing any
closures that might be present in the open formulas
-}

rebuild :: ( FirstOrder (FixLang f) 
           , MonadVar (FixLang f) (State Int)
           , StaticVar (FixLang f)) => FixLang f a -> FixLang f a
rebuild (x :!$: y) = rebuild x :!$: rebuild y
rebuild (LLam f) = LLam (\x -> subst sv x $ rebuild (f sv))
    where sv = static $ scopeHeight (LLam f)
rebuild t = t

--------------------------------------------------------
--2. Random Syntax
--------------------------------------------------------

{-|
These are data structures that will be replaced in the course of
a generating list syntax items for testing. If one thinks of the piece of
syntax as a tree, then the buds are what are replaced by blossoms as the
tree grows.
-}
data Buds f where Bud :: Typeable a => f a -> Buds f

{-|
These are data structures that will replace buds
-}
data Blossoms f where Blossom :: Typeable a => f a -> Blossoms f

bloom :: (MonadVar (FixLang f) (State Int), MonadVar (FixLang f) (StateT Int []), FirstOrder (FixLang f), UniformlyEq (FixLang f)) => 
    [Buds (FixLang f)] -> [Blossoms (FixLang f)] -> FixLang f a -> [FixLang f a]
bloom buds blossoms tree = evalStateT (sbloom buds blossoms tree) (scopeHeight tree + 1)

sbloom :: (MonadVar (FixLang f) (StateT Int []), FirstOrder (FixLang f), UniformlyEq (FixLang f)) => 
    [Buds (FixLang f)] -> [Blossoms (FixLang f)] -> FixLang f a -> StateT Int [] (FixLang f a)
sbloom buds blossoms tree = 
        do (Bud bud) <- S.lift buds
           (Blossom blossom) <- S.lift blossoms
           case tree of 
                (h :!$: t) -> 
                    do head <- S.lift [True,False]
                       if head 
                          then do h' <- sbloom buds blossoms h
                                  return $ h' :!$: t
                          else do t' <- sbloom buds blossoms t
                                  return $ h :!$: t'
                (LLam f) -> do sv <- fresh
                               f' <- sbloom buds blossoms (f sv)
                               return $ LLam $ \x -> subst sv x f'
                _ -> case (equalizeTypes bud blossom, equalizeTypes bud tree) of
                         (Just Refl, Just Refl) -> 
                            if bud =* tree 
                                then return blossom 
                                else S.lift []
                         _ -> S.lift []

grow :: (MonadVar (FixLang f) (State Int), MonadVar (FixLang f) (StateT Int []), FirstOrder (FixLang f), UniformlyEq (FixLang f), Eq (FixLang f a)) => 
    [Buds (FixLang f)] -> [Blossoms (FixLang f)] -> FixLang f a -> [[FixLang f a]]
grow buds blossoms tree = iterate (\x -> x >>= nub . bloom buds blossoms) [tree]

{-
If some of your blossoms are lambdas, you might be more pleased with the results of this function.
-}
-- betaGrow :: (MonadVar (FixLang f) (State Int), MonadVar (FixLang f) (StateT Int []), FirstOrder (FixLang f), UniformlyEq (FixLang f), Eq (FixLang f a)) => 
--     [Buds (FixLang f)] -> [Blossoms (FixLang f)] -> FixLang f a -> [[FixLang f a]]
-- betaGrow buds blossoms tree = iterate (\x -> x >>= fmap betaReduce . nub . bloom buds blossoms) [tree]
