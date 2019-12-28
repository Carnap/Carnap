module Filter.TreeDeduction (makeTreeDeduction) where

import Text.Pandoc
import Filter.Util (splitIt, intoChunks,formatChunk, unlines')
import Data.Map (fromList, toList, unions)
import Prelude

makeTreeDeduction :: Block -> Block
makeTreeDeduction cb@(CodeBlock (_,classes,extra) contents)
    | "TreeDeduction" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeTreeDeduction x = x

activate cls extra chunk
    | "propNK" `elem` cls = template (opts [("system","propNK")])
    | "propNJ" `elem` cls = template (opts [("system","propNJ")])
    | otherwise = RawBlock "html" "<div>No Matching Tree Deduction Calculus</div>"
    where numof = takeWhile (/= ' ')
          (h:t) = formatChunk chunk
          propof = dropWhile (== ' ') . dropWhile (/= ' ')
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("goal", propof h) 
                  , ("submission", "saveAs:" ++ numof h)
                  , ("type", "treedeductionchecker")
                  ]
          template opts = Div ("",["exercise"],[])
                            [ Plain 
                                [Span ("",[],[]) 
                                    [Str (numof h)]
                                ]
                            , Div ("",[],map (\(x,y) -> ("data-carnap-" ++ x,y)) $ toList opts)
                                            [Plain [Str (unlines' t)]]
                            ]
