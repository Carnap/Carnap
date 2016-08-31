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
        case (splitOn ":" l) of
            [x,y] -> "<div class=\"translate prop\"><input type =\"text\" value=\""
                                ++ y ++ "\"><div>" 
                                ++ show (simpleCipher x) ++ "</div></div>"
            _ -> "<div>No Matching Translation</div>"
    | otherwise = RawBlock "html" "<div>No Matching Translation</div>"
