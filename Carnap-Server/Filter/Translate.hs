module Filter.Translate (makeTranslate) where

import Carnap.GHCJS.SharedFunctions (simpleCipher)
import Text.Pandoc
import Data.List.Split (splitOn)
import Data.Map (fromList,toList,unions)
import Filter.Util (splitIt, intoChunks,formatChunk, unlines',sanatizeHtml)
import Prelude

makeTranslate :: Block -> Block
makeTranslate cb@(CodeBlock (_,classes,extra) contents)
    | "Translate" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeTranslate x = x

activate cls extra chunk
    | "Prop" `elem` cls = RawBlock "html" $ template (opts [("transtype","prop")])
    | "FOL" `elem` cls = RawBlock "html" $ template (opts [("transtype","first-order")])
    | otherwise = RawBlock "html" "<div>No Matching Translation</div></div>"
    where numof = takeWhile (/= ' ')
          contentof = dropWhile (== ' ') . dropWhile (/= ' ')
          (h:t) = formatChunk chunk
          fixed = case splitOn ":" (contentof h) of 
                    [x,y] -> [ ("type","translate")
                             , ("goal", show (simpleCipher x))
                             , ("problem", sanatizeHtml y)
                             , ("submission", "saveAs:" ++ numof h)
                             ]
                    _ -> []
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          template opts = "<div class=\"exercise\">"
                          ++ "<span> exercise " ++ numof h ++ "</span>"
                          ++ case splitOn ":" (contentof h) of
                              [x,y] -> "<div"
                                       ++ concatMap (\(x,y) -> " data-carnap-" ++ x ++ "=\"" ++ y ++ "\"") (toList opts)
                                       ++ ">"
                                       ++ case t of [] -> y; _ -> unlines' t
                                       ++ "</div></div>"
                              _ -> "<div>No Matching Translation</div></div>"
