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
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof cnt ++ "</span>"
        ++ "<div data-carnap-type='synchecker' data-carnap-matchtype='match'"
        ++ " data-carnap-goal='" ++ propof cnt ++ "'"
        ++ " data-carnap-submission='saveAs:" ++ numof cnt ++ "'"
        ++ ">"
        ++ "</div></div>"
    | "MatchClean" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof cnt ++ "</span>"
        ++ "<div data-carnap-type='synchecker' data-carnap-matchtype='match'"
        ++ " data-carnap-goal='" ++ propof cnt ++ "'"
        ++ " data-carnap-submission='saveAs:" ++ numof cnt ++ "'"
        ++ ">"
        ++ "</div></div>"
    | otherwise = RawBlock "html" "<div>No Matching SynChecker</div>"
    where numof x = takeWhile (/= ' ') x
          propof x = dropWhile (== ' ') . dropWhile (/= ' ') $ x
