{-# LANGUAGE OverloadedStrings #-}
module Filter.TruthTrees (makeTruthTrees) where

import           Data.Maybe
import           Data.Text   (Text)
import qualified Data.Text   as T
import           Filter.Util (contentOf, intoChunks, numof)
import           Prelude
import           Text.Pandoc
import           Util.Data

makeTruthTrees :: Block -> Block
makeTruthTrees cb@(CodeBlock (_, classes, extra) contents)
    | "TruthTree" `elem` classes = Div ("", [], []) $ map (pushExerciseParams classes extra) $ intoChunks contents
    | otherwise = cb
makeTruthTrees x = x

pushExerciseParams :: [Text] -> [(Text, Text)] -> Text -> Block
pushExerciseParams cls extra chunk
    | "Prop" `elem` cls = Div (problemElId, [], []) [
            RawBlock "html" (T.concat
                [ "\n<script>\n"
                , "document.TruthTrees ||= [];\n"
                , "document.TruthTrees.push(['"
                , problemElId
                , "', '"
                , escape . contentOf $ chunk
                , "', '"
                , escape checkFnName
                , "']);\n"
                ,"</script>\n" ])
        ]
    | otherwise = RawBlock "html" "<div>No matching truth tree logic</div>"
    where escape = T.pack . sanitizeForJS . T.unpack
          problemElId = T.concat ["problem-", numof chunk]
          -- Tableaux default to Ichikawa-Jenkins SL if not otherwise specified
          checkFnName = fromMaybe "checkIchikawaJenkinsSLTableau" $ lookup "checkFunction" extra
