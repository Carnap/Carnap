module Filter.ProofCheckers (makeProofChecker,splitIt, intoChunks,formatChunk) where

import Text.Pandoc
import Data.List.Split (splitOn)
import Data.Char (isDigit)
import Prelude

makeProofChecker :: Block -> Block
makeProofChecker cb@(CodeBlock (_,classes,_) contents)
    | "ProofChecker" `elem` classes = Div ("",[],[]) $ map (activate classes) $ intoChunks contents

    | otherwise = cb
makeProofChecker x = x

activate cls chunk
    | "Prop" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof h ++ "</span>"
        ++ "<div class=\"proofchecker prop\"><div class=\"goal\">" ++ h ++ "</div>"
        ++ "<textarea>" ++ unlines t ++ "</textarea><div class=\"output\"></div></div></div>"
    | "FirstOrder" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof h ++ "</span>"
        ++ "<div class=\"proofchecker firstOrder\"><div class=\"goal\">" ++ h ++ "</div>"
        ++ "<textarea>" ++ unlines t ++ "</textarea><div class=\"output\"></div></div></div>"
    | "LogicBook" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof h ++ "</span>"
        ++ "<div class=\"proofchecker LogicBook\"><div class=\"goal\">" ++ h ++ "</div>"
        ++ "<textarea>" ++ unlines t ++ "</textarea><div class=\"output\"></div></div></div>"
    | otherwise = RawBlock "html" "<div>No Matching Logic for Derivation</div>"
    where numof x = takeWhile (/= ' ') x
          (h:t) = formatChunk chunk

splitIt [] = ([],[])
splitIt l = case break (== '\n') l of
                (h,t@(_:x:xs)) -> if x == '|'
                                then let (h',t') = splitIt (x:xs) in
                                    (h ++ ('\n':h'),t')
                                else (h,x:xs)
                y -> y

intoChunks [] = []
intoChunks l = cons $ case splitIt l of (h,t) -> (h,intoChunks t)

formatChunk = map cleanProof . lines
    where cleanProof l@ (x:xs) = if x == '|' then dropWhile (\y -> isDigit y || (y == '.')) xs
                                             else l


cons (h,t) = h : t
