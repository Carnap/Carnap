module Filter.Sequent (makeSequent) where

import Text.Pandoc
import Filter.Util (splitIt, intoChunks,formatChunk, unlines')
import Data.Map (fromList, toList, unions)
import Prelude

makeSequent :: Block -> Block
makeSequent cb@(CodeBlock (_,classes,extra) contents)
    | "Sequent" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeSequent x = x

activate cls extra chunk
    | "propLK" `elem` cls = template (opts [("system","propLK")])
    | "propLJ" `elem` cls = template (opts [("system","propLJ")])
    | "foLK" `elem` cls = template (opts [("system","foLK")])
    | "foLJ" `elem` cls = template (opts [("system","foLJ")])
    | otherwise = RawBlock "html" "<div>No Matching Sequent Calculus</div>"
    where numof = takeWhile (/= ' ')
          (h:t) = formatChunk chunk
          propof = dropWhile (== ' ') . dropWhile (/= ' ')
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("goal", propof h) 
                  , ("submission", "saveAs:" ++ numof h)
                  , ("type", "sequentchecker")
                  ]
          template opts = Div ("",["exercise"],[])
                            [ Plain 
                                [Span ("",[],[]) 
                                    [Str (numof h)]
                                ]
                            , Div ("",[],map (\(x,y) -> ("data-carnap-" ++ x,y)) $ toList opts)
                                            [Plain [Str (unlines' t)]]
                            ]
