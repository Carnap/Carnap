{-# LANGUAGE OverloadedStrings #-}
module Filter.Translate (makeTranslate) where

import Carnap.GHCJS.SharedFunctions (simpleCipher)
import Text.Pandoc
import Data.Map (fromList,toList,unions)
import qualified Data.Text as T
import Data.Text (Text)
import Filter.Util (toDataCarnap, intoChunks,formatChunk, unlines', sanitizeHtml, exerciseWrapper, numof, contentOf)
import Prelude

makeTranslate :: Block -> Block
makeTranslate cb@(CodeBlock (_,classes,extra) contents)
    | "Translate" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeTranslate x = x

activate :: [Text] -> [(Text, Text)] -> Text -> Block
activate cls extra chunk
    | "Prop"  `elem` cls = template (opts [("transtype","prop")])
    | "FOL"   `elem` cls = template (opts [("transtype","first-order")])
    | "Desc"  `elem` cls = template (opts [("transtype","description")])
    | "Exact" `elem` cls = template (opts [("transtype","exact")])
    | otherwise = RawBlock "html" "<div>No Matching Translation</div></div>"
    where (h:t) = formatChunk chunk
          fixed = case T.splitOn ":" (contentOf h) of
                    [x,y] -> [ ("type","translate")
                             , ("goal", T.pack $ show (simpleCipher $ T.unpack x))
                             , ("problem", sanitizeHtml y)
                             , ("submission", T.concat ["saveAs:", numof h])
                             ]
                    _ -> []
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          template myOpts = exerciseWrapper (toList myOpts) (numof h) $
                                case T.splitOn ":" (contentOf h) of
                                  [_,y] -> Div ("",[], map toDataCarnap $ toList myOpts)
                                            [Plain [Str (case t of [] -> y; _ -> unlines' t)]]
                                  _ -> Div ("",[],[]) [Plain [Str "No matching Translation"]]
