{-# LANGUAGE OverloadedStrings #-}
module Filter.Util (splitIt, intoChunks, formatChunk, unlines',sanitizeHtml,
                    exerciseWrapper, contentOf, numof, toDataCarnap) where

import Prelude
import Text.Pandoc
import qualified Data.Text as T
import Data.Text (Text)
import Data.Char (isDigit)
import Text.Blaze.Html
import Text.Blaze.Html.Renderer.String

splitIt :: String -> (String, String)
splitIt [] = ([],[])
splitIt l = case break (== '\n') l of
                (h,(_:x:xs)) -> if x == '|'
                                then let (h',t') = splitIt (x:xs) in
                                     (h ++ ('\n':h'),t')
                                else (h,x:xs)
                (h,"\n") -> (h,[])
                y -> y

intoChunks' :: String -> [String]
intoChunks' [] = []
intoChunks' l = case splitIt l of
                 ([],t) -> intoChunks' t
                 (h,t) -> h : intoChunks' t

-- TODO: rewrite this code to use Data.Text primitives/idioms
intoChunks :: Text -> [Text]
intoChunks = map T.pack . intoChunks' . T.unpack

formatChunk :: Text -> [Text]
formatChunk = map (T.pack . cleanProof . T.unpack) . T.lines
    where cleanProof ('|':xs) = dropWhile (\y -> isDigit y || (y == '.')) xs
          cleanProof l = l

-- | eat the first space delimited field e.g. "a b c" -> "b c"
contentOf :: Text -> Text
contentOf = T.stripStart . snd . T.break (== ' ')

-- | grab the first field of a 'Text'
numof :: Text -> Text
numof = T.takeWhile (/= ' ')

-- | like 'T.unlines' but without a trailing newline
unlines' :: [Text] -> Text
unlines' = T.dropWhileEnd (== '\n') . T.unlines

sanitizeHtml :: ToMarkup a => a -> Text
sanitizeHtml = T.pack . renderHtml . toHtml

toDataCarnap :: (Text, Text) -> (Text, Text)
toDataCarnap (x, y) = (T.concat ["data-carnap-", x], y)

exerciseWrapper :: [(Text, Text)] -> Text -> Block -> Block
exerciseWrapper opts label content = Div (T.concat ["exercise-", label], ["exercise"],[]) (spans:[content])
    where spans = case lookup "points" opts of
                      Nothing -> Plain [Span ("",[],[]) [Str label]]
                      Just pts -> Plain [Span ("",[],[]) [Str label], Span ("",[],[]) [Str $ T.concat [pts, " pts"]] ]
