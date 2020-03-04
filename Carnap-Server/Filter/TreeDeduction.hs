module Filter.TreeDeduction (makeTreeDeduction) where

import Text.Pandoc
import Filter.Util (splitIt, intoChunks,formatChunk, unlines')
import Data.Map (fromList, toList, unions)
import Prelude

makeTreeDeduction :: Block -> Block
makeTreeDeduction cb@(CodeBlock (_,classes,extra) contents)
    | "TreeDeduction" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | "TreePlayground" `elem` classes = Div ("",[],[]) [toPlayground classes extra contents]
    | otherwise = cb
makeTreeDeduction x = x

activate cls extra chunk
    | "propNK" `elem` cls = template (opts [("system","propNK")])
    | "propNJ" `elem` cls = template (opts [("system","propNJ")])
    | "openLogicNK" `elem` cls = template (opts [("system","openLogicNK")])
    | otherwise = template (opts [])
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

toPlayground cls extra contents
    | "propNK" `elem` cls = template (opts [("system","propNK")])
    | "propNJ" `elem` cls = template (opts [("system","propNJ")])
    | "openLogicNK" `elem` cls = template (opts [("system","openLogicNK")])
    | otherwise = template (opts [])
    where numof = takeWhile (/= ' ')
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type", "treedeductionchecker") ]
          template opts = Div ("",["exercise"],[])
                            [ Plain 
                                [Span ("",[],[]) 
                                    [Str "Playground"]
                                ]
                            , Div ("",[],map (\(x,y) -> ("data-carnap-" ++ x,y)) $ toList opts)
                                            [Plain [Str (unlines' $ formatChunk contents)]]
                            ]
