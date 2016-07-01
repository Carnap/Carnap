{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Util(
    Nat(Zero, Succ), Vec(VNil, VCons),
    crossWith, bigCrossWith, bigCrossWithH,
    bigUnionWith, bigUnion,
    EveryPig(..), AnyPig(..),
    pop
) where

import Data.List
import Control.Lens
import Data.Typeable
import Control.Monad.State

pop :: State [a] a
pop = do
  (x:xs) <- get
  put xs
  return x

--define natural numbers for type lifting
data Nat = Zero
         | Succ Nat
    deriving(Eq, Ord)

toInt Zero = 0
toInt (Succ n) = 1 + toInt n

instance Show Nat where
    show n = show $ toInt n

instance Num Nat where
  x + Zero = x
  (Succ x) + y = Succ (x + y)
  Zero + y = y

  x * Zero = Zero
  (Succ x) * y = y + (x * y)
  Zero * y = Zero

  abs x = x

  signum _ = 1

  fromInteger 0 = Zero
  fromInteger n = Succ (fromInteger $ n - 1)

  x - Zero = x
  Zero - y = Zero
  (Succ x) - (Succ y) = x - y

  negate = error "negation is not defined on naturals"

-- | the standard hello world dependent types examples. a list where the size
-- | are known at the type level
data Vec :: Nat -> * -> * where
    VNil :: Vec Zero arg
    VCons :: arg -> Vec n arg -> Vec (Succ n) arg

class Plated a' => MultiPlated a a' where
    multiplate :: Simple Traversal a a'

instance Plated a => MultiPlated a a where
    multiplate = id

bigUnion :: Eq a => [[a]] -> [a]
bigUnion = bigUnionWith id
bigUnionWith f xss = foldr union [] (map f xss)
crossWith f xs ys = [f x y | x <- xs, y <- ys]
bigCrossWith f xs xss = foldr (crossWith f) xs xss
bigCrossWithH f (xs:xss) = bigCrossWith f xs xss
bigCrossWithH _ []       = []

newtype EveryPig f = EveryPig {unEveryPig :: forall a. f a}
--the typeable constraint lets us unpack this in a safe way
data AnyPig f where
    AnyPig :: Typeable a => f a -> AnyPig f

--class UniformlyEq f where
  --  eq :: f a -> f b -> Bool
    --eq x y = not (neq x y)
    --neq :: f a -> f b -> Bool

--instance UniformlyEq f => Eq (AnyPig f) where
  --  (AnyPig x) == (AnyPig y) = eq x y
