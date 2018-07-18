module Filter.SynCheckers (makeSynCheckers) where

import Text.Pandoc
import Data.Map (fromList, toList, unions)
import Prelude

makeSynCheckers :: Block -> Block
makeSynCheckers cb@(CodeBlock (_,classes,extra) contents)
    | "SynChecker" `elem` classes = Div ("",[],[]) $ map (activate classes extra) (lines contents)
    | otherwise = cb
makeSynCheckers x = x

activate cls extra cnt
    | "Match" `elem` cls = RawBlock "html" $ template (opts [("matchtype","match")])
    | "MatchClean" `elem` cls = RawBlock "html" $ template (opts [("matchtype","matchclean")])
    | otherwise = RawBlock "html" "<div>No Matching SynChecker</div>"
    where numof x = takeWhile (/= ' ') x
          propof x = dropWhile (== ' ') . dropWhile (/= ' ') $ x
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","synchecker")
                  , ("goal", propof cnt) 
                  , ("submission", "saveAs:" ++ numof cnt)
                  ]
          template opts = "<div class=\"exercise\">"
                          ++ "<span> exercise " ++ numof cnt ++ "</span><div"
                          ++ concatMap (\(x,y) -> " data-carnap-" ++ x ++ "=\"" ++ y ++ "\"") (toList opts)
                          ++ "'>" 
                          ++ "</div></div>" 
