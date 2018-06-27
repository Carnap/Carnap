module Filter.Util (splitIt, intoChunks,formatChunk, unlines') where

import Prelude
import Data.Char (isDigit)

splitIt [] = ([],[])
splitIt l = case break (== '\n') l of
                (h,t@(_:x:xs)) -> if x == '|'
                                then let (h',t') = splitIt (x:xs) in
                                     (h ++ ('\n':h'),t')
                                else (h,x:xs)
                y -> y

intoChunks [] = []
intoChunks l = let (h,t) = splitIt l in h : intoChunks t

formatChunk = map cleanProof . lines
    where cleanProof ('|':xs) = dropWhile (\y -> isDigit y || (y == '.')) xs
          cleanProof l = l

unlines' [] = ""
unlines' (x:[]) = x
unlines' (x:xs) = x ++ '\n':unlines' xs
