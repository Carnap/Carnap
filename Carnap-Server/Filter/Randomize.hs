{-# LANGUAGE PatternGuards #-}
module Filter.Randomize (randomizeProblems) where

import           Data.Hashable
import           Data.List
import           Prelude
import           System.Random
import           Text.Pandoc

randomizeProblems :: Int -> Block -> Block
randomizeProblems salt (Div ("",[],[]) contents) = Div ("",[],[]) (randomize salt contents)
randomizeProblems _ x = x

randomize :: Int -> [Block] -> [Block]
randomize salt = map pickOne . groupBy sameEx
    where sameEx a b | Just x <- exercise a, Just y <- exercise b, x == y = True
                     | otherwise = False
          --TODO: match on data-carnap-label rather than inspecting span
          exercise (Div (_,["exercise"],_) (Plain (Span _ [Str h]:_):_)) = Just h
          exercise _ = Nothing
          pickOne l =  l !! (fst $ randomR (0,length l - 1) (mkStdGen (hashWithSalt salt (exercise $ head l))))
