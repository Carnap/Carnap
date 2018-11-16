{-#LANGUAGE GADTs #-}

module Carnap.Core.Util( crossWith, bigCrossWith, bigCrossWithH, ListComp(..)
) where

data ListComp f a where
    ListComp :: [f a] -> ListComp f a

crossWith f xs ys = [f x y | x <- xs, y <- ys]
bigCrossWith f xs xss = foldr (crossWith f) xs xss
bigCrossWithH f (xs:xss) = bigCrossWith f xs xss
bigCrossWithH _ []       = []
