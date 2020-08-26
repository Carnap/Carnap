{-# LANGUAGE OverloadedStrings #-}
module Filter.TruthTables (makeTruthTables) where

import Text.Pandoc
import Filter.Util (toDataCarnap, contentOf, intoChunks, formatChunk, unlines', exerciseWrapper)
import qualified Data.Text as T
import Data.Text (Text)
import Data.Map (Map, fromList, toList, unions)
import Prelude

makeTruthTables :: Block -> Block
makeTruthTables cb@(CodeBlock (_,classes,extra) contents)
    | "TruthTable" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeTruthTables x = x


activate :: [Text] -> [(Text, Text)] -> Text -> Block
activate cls extra chunk
    | "Simple" `elem` cls = template (opts [("tabletype","simple")])
    | "Validity" `elem` cls = template (opts [("tabletype","validity")])
    | "Partial" `elem` cls = template (opts [("tabletype","partial")])
    | otherwise = RawBlock "html" "<div>No Matching Truth Table Type</div>"
    where numof x = T.takeWhile (/= ' ') x
          (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","truthtable")
                  , ("goal", contentOf h)
                  , ("submission", T.concat ["saveAs:", numof h])
                  ]
          template :: Map Text Text -> Block
          template myOpts = exerciseWrapper (toList myOpts) (numof h) $ Div
                                ("",[], map toDataCarnap $ toList myOpts)
                                [Plain [Str (unlines' t)]]
