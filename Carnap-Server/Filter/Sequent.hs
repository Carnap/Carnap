module Filter.Sequent (makeSequent) where

import Text.Pandoc
import Filter.Util (toDataCarnap, numof, contentOf, intoChunks, formatChunk, unlines', exerciseWrapper)
import Data.Map (fromList, toList, unions)
import qualified Data.Text as T
import Data.Text (Text)
import Prelude

makeSequent :: Block -> Block
makeSequent cb@(CodeBlock (_,classes,extra) contents)
    | "Sequent" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | "SequentPlayground" `elem` classes = Div ("",[],[]) $ [toPlayground classes extra contents]
    | otherwise = cb
makeSequent x = x

activate :: [Text] -> [(Text, Text)] -> Text -> Block
activate cls extra chunk
    | "propLK" `elem` cls = template (opts [("system","propLK")])
    | "propLJ" `elem` cls = template (opts [("system","propLJ")])
    | "openLogicPropLK" `elem` cls = template (opts [("system","openLogicPropLK")])
    | "openLogicPropLJ" `elem` cls = template (opts [("system","openLogicPropLJ")])
    | "foLK" `elem` cls = template (opts [("system","foLK")])
    | "foLJ" `elem` cls = template (opts [("system","foLJ")])
    | "openLogicFOLK" `elem` cls = template (opts [("system","openLogicFOLK")])
    | "openLogicFOLJ" `elem` cls = template (opts [("system","openLogicFOLJ")])
    | otherwise = RawBlock "html" "<div>No Matching Sequent Calculus</div>"
    where (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("goal", contentOf h)
                  , ("submission", T.concat ["saveAs:", numof h])
                  , ("type", "sequentchecker")
                  ]
          template myOpts = exerciseWrapper (toList myOpts) (numof h) $ Div
                                ("",[], map toDataCarnap $ toList myOpts)
                                [Plain [RawInline "html" (unlines' t)]]
                                --XXX: need raw inline rather than Str
                                --because of pandoc issue 5469

toPlayground :: [Text] -> [(Text, Text)] -> Text -> Block
toPlayground cls extra content
    | "propLK" `elem` cls = template (opts [("system","propLK")])
    | "propLJ" `elem` cls = template (opts [("system","propLJ")])
    | "openLogicPropLK" `elem` cls = template (opts [("system","openLogicPropLK")])
    | "openLogicPropLJ" `elem` cls = template (opts [("system","openLogicPropLJ")])
    | "foLK" `elem` cls = template (opts [("system","foLK")])
    | "foLJ" `elem` cls = template (opts [("system","foLJ")])
    | "openLogicFOLK" `elem` cls = template (opts [("system","openLogicFOLK")])
    | "openLogicFOLJ" `elem` cls = template (opts [("system","openLogicFOLJ")])
    | otherwise = RawBlock "html" "<div>No Matching Sequent Calculus</div>"
    where opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type", "sequentchecker") ]
          template myOpts = exerciseWrapper (toList myOpts) "Playground" $ Div
                                ("",[], map toDataCarnap $ toList myOpts)
                                [Plain [RawInline "html" (unlines' $ formatChunk content)]]
