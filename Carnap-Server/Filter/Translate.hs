module Filter.Translate (makeTranslate) where

import Carnap.GHCJS.SharedFunctions (simpleCipher)
import Text.Pandoc
import Data.List.Split (splitOn)
import Data.Map (fromList,toList,unions)
import Filter.Util (splitIt, intoChunks,formatChunk, unlines',sanatizeHtml, exerciseWrapper)
import Prelude

makeTranslate :: Block -> Block
makeTranslate cb@(CodeBlock (_,classes,extra) contents)
    | "Translate" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeTranslate x = x

activate cls extra chunk
    | "Prop" `elem` cls = template (opts [("transtype","prop")])
    | "FOL" `elem` cls = template (opts [("transtype","first-order")])
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
          template opts = exerciseWrapper (toList opts) (numof h) $ 
                                case splitOn ":" (contentof h) of
                                  [x,y] -> Div ("",[],map (\(x,y) -> ("data-carnap-" ++ x,y)) $ toList opts) 
                                            [Plain [Str (case t of [] -> y; _ -> unlines' t)]]
                                  _ -> Div ("",[],[]) [Plain [Str "No matching Translation"]]
