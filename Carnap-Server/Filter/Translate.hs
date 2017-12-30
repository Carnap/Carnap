module Filter.Translate (makeTranslate) where

import Carnap.GHCJS.SharedFunctions (simpleCipher)
import Text.Pandoc
import Data.List.Split (splitOn)
import Prelude

makeTranslate :: Block -> Block
makeTranslate cb@(CodeBlock (_,classes,_) contents)
    | "Translate" `elem` classes = Div ("",[],[]) $ map (activate classes) $ lines contents

    | otherwise = cb
makeTranslate x = x

activate cls l
    | "Prop" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof l ++ "</span>"
        ++ case splitOn ":" (contentof l) of
            [x,y] -> "<div data-carnap-type='translate'"
                     ++ " data-carnap-transtype='prop'"
                     ++ " data-carnap-submission='saveAs:" ++ numof l ++ "'"
                     ++ " data-carnap-goal='" ++ show (simpleCipher x) ++ "'"
                     ++ ">"
                     ++ y 
                     ++ "</div></div>"
            _ -> "<div>No Matching Translation</div></div>"
    | "FOL" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof l ++ "</span>"
        ++ case splitOn ":" (contentof l) of
            [x,y] -> "<div data-carnap-type='translate'"
                     ++ " data-carnap-transtype='first-order'"
                     ++ " data-carnap-submission='saveAs:" ++ numof l ++ "'"
                     ++ " data-carnap-goal='" ++ show (simpleCipher x) ++ "'"
                     ++ ">"
                     ++ y 
                     ++ "</div></div>"
            _ -> "<div>No Matching Translation</div></div>"
    | otherwise = RawBlock "html" "<div>No Matching Translation</div></div>"
    where numof = takeWhile (/= ' ')
          contentof = dropWhile (== ' ') . dropWhile (/= ' ')
