{-# LANGUAGE OverloadedStrings #-}
module Filter.TreeDeduction (makeTreeDeduction) where

import Text.Pandoc
import Filter.Util (toDataCarnap, contentOf, intoChunks,formatChunk, unlines', exerciseWrapper)
import Data.Map (fromList, toList, unions)
import qualified Data.Text as T
import Data.Text (Text)
import Prelude

makeTreeDeduction :: Block -> Block
makeTreeDeduction cb@(CodeBlock (_,classes,extra) contents)
    | "TreeDeduction" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | "TreePlayground" `elem` classes = Div ("",[],[]) [toPlayground classes extra contents]
    | otherwise = cb
makeTreeDeduction x = x

activate :: [Text] -> [(Text, Text)] -> Text -> Block
activate cls extra chunk
    | "propNK" `elem` cls = template (opts [("system","propNK")])
    | "propNJ" `elem` cls = template (opts [("system","propNJ")])
    | "openLogicNK" `elem` cls = template (opts [("system","openLogicNK")])
    | "openLogicFOLNK" `elem` cls = template (opts [("system","openLogicFOLNK")])
    | "openLogicSTNK" `elem` cls = template (opts [("system","openLogicSTNK")])
    | "openLogicExSTNK" `elem` cls = template (opts [("system","openLogicExSTNK")])
    | "openLogicESTNK" `elem` cls = template (opts [("system","openLogicESTNK")])
    | "openLogicExESTNK" `elem` cls = template (opts [("system","openLogicExESTNK")])
    | "openLogicSSTNK" `elem` cls = template (opts [("system","openLogicSSTNK")])
    | "openLogicExSSTNK" `elem` cls = template (opts [("system","openLogicExSSTNK")])
    | "openLogicArithNK" `elem` cls = template (opts [("system","openLogicArithNK")])
    | "openLogicExArithNK" `elem` cls = template (opts [("system","openLogicExArithNK")])
    | "openLogicExHOArithNK" `elem` cls = template (opts [("system","openLogicExHOArithNK")])
    | otherwise = template (opts [])
    where numof = T.takeWhile (/= ' ')
          (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("goal", contentOf h)
                  , ("submission", T.concat ["saveAs:", numof h])
                  , ("type", "treedeductionchecker")
                  ]
          template myOpts = exerciseWrapper (toList myOpts) (numof h) $ Div
                                ("",[], map toDataCarnap $ toList myOpts)
                                [Plain [RawInline "html" (unlines' t)]]
                                --XXX: need raw inline rather than Str
                                --because of pandoc issue 5469

toPlayground :: [Text] -> [(Text, Text)] -> Text -> Block
toPlayground cls extra contents
    | "propNK" `elem` cls = template (opts [("system","propNK")])
    | "propNJ" `elem` cls = template (opts [("system","propNJ")])
    | "openLogicNK" `elem` cls = template (opts [("system","openLogicNK")])
    | "openLogicFOLNK" `elem` cls = template (opts [("system","openLogicFOLNK")])
    | "openLogicSTNK" `elem` cls = template (opts [("system","openLogicSTNK")])
    | "openLogicExSTNK" `elem` cls = template (opts [("system","openLogicExSTNK")])
    | "openLogicESTNK" `elem` cls = template (opts [("system","openLogicESTNK")])
    | "openLogicExESTNK" `elem` cls = template (opts [("system","openLogicExESTNK")])
    | "openLogicSSTNK" `elem` cls = template (opts [("system","openLogicSSTNK")])
    | "openLogicExSSTNK" `elem` cls = template (opts [("system","openLogicExSSTNK")])
    | "openLogicArithNK" `elem` cls = template (opts [("system","openLogicArithNK")])
    | "openLogicExArithNK" `elem` cls = template (opts [("system","openLogicExArithNK")])
    | "openLogicExHOArithNK" `elem` cls = template (opts [("system","openLogicExHOArithNK")])
    | otherwise = template (opts [])
    where opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type", "treedeductionchecker") ]
          template myOpts = Div ("",["exercise"],[])
                            [ Plain
                                [Span ("",[],[])
                                    [Str "Playground"]
                                ]
                            , Div ("",[], map toDataCarnap $ toList myOpts)
                                            [Plain [RawInline "html" (unlines' $ formatChunk contents)]]
                            ]
