module Filter.ProofCheckers (makeProofChecker) where

import Text.Pandoc
import Data.List.Split (splitOn)
import Prelude

makeProofChecker :: Block -> Block
makeProofChecker cb@(CodeBlock (_,classes,_) contents)
    | "ProofChecker" `elem` classes = Div ("",[],[]) $ map (activate classes) $ lines contents

    | otherwise = cb
makeProofChecker x = x

activate cls l
    | "Prop" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof l ++ "</span>"
        ++ "<div class=\"proofchecker prop\"><div class=\"goal\">" 
            ++ l ++ "</div><textarea></textarea><div class=\"output\"></div></div></div>"
    | "FirstOrder" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof l ++ "</span>"
        ++ "<div class=\"proofchecker firstOrder\"><div class=\"goal\">" 
            ++ l ++ "</div><textarea></textarea><div class=\"output\"></div></div></div>"
    | "LogicBook" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof l ++ "</span>"
        ++ "<div class=\"proofchecker LogicBook\"><div class=\"goal\">" 
            ++ l ++ "</div><textarea></textarea><div class=\"output\"></div></div></div>"
    | otherwise = RawBlock "html" "<div>No Matching Logic for Derivation</div>"
    where numof x = takeWhile (/= ' ') x
