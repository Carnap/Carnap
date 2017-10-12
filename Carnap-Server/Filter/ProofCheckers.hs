module Filter.ProofCheckers (makeProofChecker,splitIt, intoChunks,formatChunk) where

import Text.Pandoc
import Data.List.Split (splitOn)
import Data.Char (isDigit)
import Prelude

makeProofChecker :: Block -> Block
makeProofChecker cb@(CodeBlock (_,classes,_) contents)
    | "ProofChecker" `elem` classes = Div ("",[],[]) $ map (activate classes) $ intoChunks contents
    | "Playground" `elem` classes = Div ("",[],[]) [toPlayground contents]
    | otherwise = cb
makeProofChecker x = x

activate cls chunk
    | "Prop" `elem` cls = actTemplate "proofchecker prop"
    | "Prop_practice" `elem` cls = actTemplate "proofchecker prop NoSub"
    | "FirstOrder" `elem` cls = actTemplate "proofchecker firstOrder"
    | "SecondOrder" `elem` cls = actTemplate "proofchecker secondOrder"
    | "PolySecondOrder" `elem` cls = actTemplate "proofchecker polyadicSecondOrder"
    | "LogicBook" `elem` cls = actTemplate "proofchecker LogicBook"
    | "ForallxSL" `elem` cls = actTemplate "proofchecker magnusSL Render"
    | "ForallxSLPlus" `elem` cls = actTemplate "proofchecker magnusSLPlus Render"
    | "ForallxQL" `elem` cls = actTemplate "proofchecker magnusQL Render"
    | "HardegreeSL" `elem` cls = actTemplate "proofchecker hardegreeSL Render"
    | "HardegreeWTL" `elem` cls = actTemplate "proofchecker hardegreeWTL Render guides"
    | otherwise = RawBlock "html" "<div>No Matching Logic for Derivation</div>"
    where numof = takeWhile (/= ' ')
          (h:t) = formatChunk chunk
          actTemplate opts = RawBlock "html" $ 
                "<div class=\"exercise\">"
                ++ "<span> exercise " ++ numof h ++ "</span>"
                ++ "<div class=\"" ++ opts ++ "\"><div class=\"goal\">" ++ h ++ "</div>"
                ++ "<textarea>" ++ unlines t ++ "</textarea><div class=\"output\"></div></div></div>"

splitIt [] = ([],[])
splitIt l = case break (== '\n') l of
                (h,t@(_:x:xs)) -> if x == '|'
                                then let (h',t') = splitIt (x:xs) in
                                    (h ++ ('\n':h'),t')
                                else (h,x:xs)
                y -> y

intoChunks [] = []
intoChunks l = cons $ case splitIt l of (h,t) -> (h,intoChunks t)
    where cons (h,t) = h : t

toPlayground contents = RawBlock "html" $
        "<div class=\"exercise\">"
        ++ "<span> playground </span>"
        ++ "<div class=\"proofchecker playground\"><div class = \"goal\"></div>"
        ++ "<textarea>" ++ contents ++ "</textarea><div class=\"output\"></div></div></div>"

formatChunk = map cleanProof . lines
    where cleanProof l@ (x:xs) = if x == '|' then dropWhile (\y -> isDigit y || (y == '.')) xs
                                             else l

