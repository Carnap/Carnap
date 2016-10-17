module Filter.TruthTables
        (makeTruthTables)
    where

import Text.Pandoc
import Prelude

makeTruthTables :: Block -> Block
makeTruthTables cb@(CodeBlock (_,classes,_) contents)
    | "TruthTable" `elem` classes = Div ("",[],[]) $ map (activate classes) (lines contents)
    | otherwise = cb
makeTruthTables x = x

activate cls cnt
    | "Simple" `elem` cls = RawBlock "html" $ 
        "<div class=\"truthtable\"><div></div><div>" 
        ++ cnt ++ "</div></div>"
    | otherwise = RawBlock "html" "<div>No Matching TruthTable</div>"
