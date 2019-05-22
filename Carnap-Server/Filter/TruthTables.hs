module Filter.TruthTables (makeTruthTables) where

import Text.Pandoc
import Filter.Util (splitIt, intoChunks,formatChunk, unlines')
import Data.Map (fromList, toList, unions)
import Prelude

makeTruthTables :: Block -> Block
makeTruthTables cb@(CodeBlock (_,classes,extra) contents)
    | "TruthTable" `elem` classes = Div ("problem",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeTruthTables x = x

activate cls extra chunk
    | "Simple" `elem` cls = RawBlock "html" $ template (opts [("tabletype","simple")])
    | "Validity" `elem` cls = RawBlock "html" $ template (opts [("tabletype","validity")])
    | "Partial" `elem` cls = RawBlock "html" $ template (opts [("tabletype","partial")])
    | otherwise = RawBlock "html" "<div>No Matching TruthTable</div>"
    where numof x = takeWhile (/= ' ') x
          contentOf x = dropWhile (== ' ') . dropWhile (/= ' ') $  x
          (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","truthtable")
                  , ("goal", contentOf h) 
                  , ("submission", "saveAs:" ++ numof h)
                  ]
          template opts = "<div class=\"exercise\">"
                          ++ "<span> exercise " ++ numof h ++ "</span><div"
                          ++ concatMap (\(x,y) -> " data-carnap-" ++ x ++ "=\"" ++ y ++ "\"") (toList opts)
                          ++ ">" 
                          ++ unlines' t
                          ++ "</div></div>" 
