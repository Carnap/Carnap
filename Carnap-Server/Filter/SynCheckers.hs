module Filter.SynCheckers (makeSynCheckers) where

import Text.Pandoc
import Filter.Util (toDataCarnap, numof, contentOf, exerciseWrapper)
import Data.Map (fromList, toList, unions)
import qualified Data.Text as T
import Data.Text (Text)
import Prelude

makeSynCheckers :: Block -> Block
makeSynCheckers cb@(CodeBlock (_,classes,extra) contents)
    | "SynChecker" `elem` classes = Div ("",[],[]) $ map (activate classes extra) (T.lines contents)
    | otherwise = cb
makeSynCheckers x = x

activate :: [Text] -> [(Text, Text)] -> Text -> Block
activate cls extra cnt
    | "Match" `elem` cls = template (opts [("matchtype","match")])
    | "MatchClean" `elem` cls = template (opts [("matchtype","matchclean")])
    | otherwise = RawBlock "html" "<div>No Matching SynChecker</div>"
    where opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","synchecker")
                  , ("goal", contentOf cnt)
                  , ("submission", T.concat ["saveAs:", numof cnt])
                  ]
          template myOpts = exerciseWrapper (toList myOpts) (numof cnt) $ Div
                                ("",[],map toDataCarnap $ toList myOpts)
                                []
