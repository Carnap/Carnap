module Filter.SynCheckers (makeSynCheckers) where

import Text.Pandoc
import Prelude

makeSynCheckers :: Block -> Block
makeSynCheckers cb@(CodeBlock (_,classes,_) contents)
    | "SynChecker" `elem` classes = Div ("",[],[]) $ map (activate classes) (lines contents)
    | otherwise = cb
makeSynCheckers x = x

activate cls cnt
    | "Match" `elem` cls = RawBlock "html" $ 
        "<div class=\"synchecker match container\"><input></input><div class=\"tree\">" 
        ++ cnt 
        ++ "</div></div>"
    | "MatchClean" `elem` cls = RawBlock "html" $ 
        "<div class=\"synchecker matchclean container\"><input></input><div class=\"tree\">" 
        ++ cnt 
        ++ "</div></div>"
    | otherwise = RawBlock "html" "<div>No Matching SynChecker</div>"
