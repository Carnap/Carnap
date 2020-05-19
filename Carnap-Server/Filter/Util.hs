module Filter.Util (splitIt, intoChunks,formatChunk, unlines',sanatizeHtml, exerciseWrapper) where

import Prelude
import Text.Pandoc
import Data.Char (isDigit)
import Text.Blaze.Html
import Text.Blaze.Html.Renderer.String

splitIt [] = ([],[])
splitIt l = case break (== '\n') l of
                (h,t@(_:x:xs)) -> if x == '|'
                                then let (h',t') = splitIt (x:xs) in
                                     (h ++ ('\n':h'),t')
                                else (h,x:xs)
                (h,"\n") -> (h,[])
                y -> y

intoChunks [] = []
intoChunks l = case splitIt l of 
                 ([],t) -> intoChunks t
                 (h,t) -> h : intoChunks t

formatChunk = map cleanProof . lines
    where cleanProof ('|':xs) = dropWhile (\y -> isDigit y || (y == '.')) xs
          cleanProof l = l

unlines' [] = ""
unlines' (x:[]) = x
unlines' (x:xs) = x ++ '\n':unlines' xs

sanatizeHtml = renderHtml . toHtml

exerciseWrapper opts label content = Div ("exercise-" ++ label,["exercise"],[]) (spans:[content])
    where spans = case lookup "points" opts of
                      Nothing -> Plain [Span ("",[],[]) [Str label]]
                      Just pts -> Plain [Span ("",[],[]) [Str label], Span ("",[],[]) [Str $ pts ++ " pts"] ] 
