module Filter.Translate (makeTranslate) where

import Carnap.GHCJS.SharedFunctions (simpleCipher)
import Text.Pandoc
import Data.List.Split (splitOn)
import Filter.Util (splitIt, intoChunks,formatChunk, unlines',sanatizeHtml)
import Prelude

makeTranslate :: Block -> Block
makeTranslate cb@(CodeBlock (_,classes,_) contents)
    | "Translate" `elem` classes = Div ("",[],[]) $ map (activate classes) $ intoChunks contents
    | otherwise = cb
makeTranslate x = x

activate cls chunk
    | "Prop" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof h ++ "</span>"
        ++ case splitOn ":" (contentof h) of
            [x,y] -> "<div data-carnap-type='translate'"
                     ++ " data-carnap-transtype='prop'"
                     ++ " data-carnap-submission='saveAs:" ++ numof h ++ "'"
                     ++ " data-carnap-goal='" ++ show (simpleCipher x) ++ "'"
                     ++ " data-carnap-problem='" ++ sanatizeHtml y ++ "'"
                     ++ ">"
                     ++ case t of [] -> y; _ -> unlines' t
                     ++ "</div></div>"
            _ -> "<div>No Matching Translation</div></div>"
    | "FOL" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof h ++ "</span>"
        ++ case splitOn ":" (contentof h) of
            [x,y] -> "<div data-carnap-type='translate'"
                     ++ " data-carnap-transtype='first-order'"
                     ++ " data-carnap-submission='saveAs:" ++ numof h ++ "'"
                     ++ " data-carnap-goal='" ++ show (simpleCipher x) ++ "'"
                     ++ " data-carnap-problem='" ++ sanatizeHtml y ++ "'"
                     ++ ">"
                     ++ case t of [] -> y; _ -> unlines' t
                     ++ "</div></div>"
            _ -> "<div>No Matching Translation</div></div>"
    | otherwise = RawBlock "html" "<div>No Matching Translation</div></div>"
    where numof = takeWhile (/= ' ')
          contentof = dropWhile (== ' ') . dropWhile (/= ' ')
          (h:t) = formatChunk chunk
