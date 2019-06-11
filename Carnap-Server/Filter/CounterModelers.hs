module Filter.CounterModelers (makeCounterModelers) where

import Text.Pandoc
import Filter.Util (splitIt, intoChunks,formatChunk, unlines')
import Data.Map (fromList, toList, unions)
import Prelude

makeCounterModelers :: Block -> Block
makeCounterModelers cb@(CodeBlock (_,classes,extra) contents)
    | "CounterModeler" `elem` classes = Div ("problem",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeCounterModelers x = x

activate cls extra chunk
    | "Simple" `elem` cls = RawBlock "html" $ template (opts [("countermodelertype","simple")])
    | "Validity" `elem` cls = RawBlock "html" $ template (opts [("countermodelertype","validity")])
    | otherwise = RawBlock "html" "<div>No Matching CounterModeler Type</div>"
    where numof x = takeWhile (/= ' ') x
          contentOf x = dropWhile (== ' ') . dropWhile (/= ' ') $  x
          (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","countermodeler")
                  , ("goal", contentOf h) 
                  , ("submission", "saveAs:" ++ numof h)
                  ]
          template opts = "<div class=\"exercise\">"
                          ++ "<span> exercise " ++ numof h ++ "</span><div"
                          ++ concatMap (\(x,y) -> " data-carnap-" ++ x ++ "=\"" ++ y ++ "\"") (toList opts)
                          ++ ">" 
                          ++ unlines' t
                          ++ "</div></div>" 
