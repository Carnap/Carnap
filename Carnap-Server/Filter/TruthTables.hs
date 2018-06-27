module Filter.TruthTables (makeTruthTables) where

import Text.Pandoc
import Filter.Util (splitIt, intoChunks,formatChunk, unlines')
import Prelude

makeTruthTables :: Block -> Block
makeTruthTables cb@(CodeBlock (_,classes,_) contents)
    | "TruthTable" `elem` classes = Div ("problem",[],[]) $ map (activate classes) $ intoChunks contents
    | otherwise = cb
makeTruthTables x = x

activate cls chunk
    | "Simple" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof h ++ "</span>"
        ++ "<div data-carnap-type='truthtable'"
        ++ " data-carnap-tabletype='simple'"
        ++ " data-carnap-goal='" ++ contentOf h ++ "'"
        ++ " data-carnap-submission='saveAs:" ++ numof h ++ "'>"
        ++ unlines' t
        ++ "</div></div>" 
    | "Validity" `elem` cls = RawBlock "html" $ 
        "<div class=\"exercise\">"
        ++ "<span> exercise " ++ numof h ++ "</span>"
        ++ "<div data-carnap-type='truthtable'"
        ++ " data-carnap-tabletype='validity'"
        ++ " data-carnap-goal='" ++ contentOf h ++ "'"
        ++ " data-carnap-submission='saveAs:" ++ numof h ++ "'>" 
        ++ unlines' t
        ++ "</div></div>" 
    | otherwise = RawBlock "html" "<div>No Matching TruthTable</div>"
    where numof x = takeWhile (/= ' ') x
          contentOf x = dropWhile (== ' ') . dropWhile (/= ' ') $  x
          (h:t) = formatChunk chunk
