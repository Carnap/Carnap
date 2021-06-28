module Filter.CounterModelers (makeCounterModelers) where

import Text.Pandoc
import Filter.Util (numof, contentOf, toDataCarnap, intoChunks,formatChunk, unlines', exerciseWrapper)
import Data.Map (fromList, toList, unions)
import qualified Data.Text as T
import Data.Text (Text)
import Prelude

makeCounterModelers :: Block -> Block
makeCounterModelers cb@(CodeBlock (_,classes,extra) contents)
    | "CounterModeler" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeCounterModelers x = x

activate :: [Text] -> [(Text, Text)] -> Text -> Block
activate cls extra chunk
    | "Simple" `elem` cls = template (opts [("countermodelertype","simple")])
    | "Validity" `elem` cls = template (opts [("countermodelertype","validity")])
    | "Constraint" `elem` cls = template (opts [("countermodelertype","constraint")])
    | otherwise = RawBlock "html" "<div>No Matching CounterModeler Type</div>"
    where (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","countermodeler")
                  , ("goal", contentOf h)
                  , ("submission", T.concat ["saveAs:", numof h])
                  ]
          template myOpts = exerciseWrapper (toList myOpts) (numof h) $
                                Div ("",[], map toDataCarnap $ toList myOpts)
                                 [ Plain [Str $ unlines' t ]]
