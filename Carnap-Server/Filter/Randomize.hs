module Filter.Randomize (randomizeProblems) where

import Data.List
import Data.Hashable
import Text.Pandoc
import System.Random
import Prelude

randomizeProblems :: Int -> Block -> Block
randomizeProblems salt (Div ("",[],[]) contents) = Div ("",[],[]) (randomize salt contents)
randomizeProblems _ x = x

randomize :: Int -> [Block] -> [Block]
randomize salt = map pickOne . groupBy sameEx
    where sameEx a b | Just x <- exercise a, Just y <- exercise b, x == y = True
                     | otherwise = False
          exercise (Div (_,["exercise"],[]) (Plain [Span _ [Str h]]:_)) = Just h
          exercise _ = Nothing
          pickOne l =  l !! (fst $ randomR (0,length l - 1) (mkStdGen (hashWithSalt salt (exercise $ head l))))
