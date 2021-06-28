module Filter.Sidenotes (makeSideNotes
) where

import Text.Pandoc
import Prelude
import qualified Data.Text as T
import Data.List (intersperse)
import Control.Monad.State

makeSideNotes :: Inline -> State Int Inline
makeSideNotes i = do n <- get
                     modify (1 +)
                     return $ pureMakeSideNotes i n

pureMakeSideNotes :: Inline -> Int -> Inline
pureMakeSideNotes i@(Note (Para ((Str s:_)):_)) n =
        case T.head s of
            ':' -> Span nullAttr [rawHead n, processNote i]
            _ -> i
pureMakeSideNotes x _ = x

toInline :: Block -> Inline
toInline (Plain xs) = Span nullAttr xs
toInline (Para xs) = Span nullAttr xs
toInline (CodeBlock a s) = Code a s
toInline (RawBlock f s) = RawInline f s
--not handling the other block constructors for now.
toInline _ = Span nullAttr []

breakInlines :: [Block] -> [Inline]
breakInlines = intersperse LineBreak . map toInline

sidenoteAttr :: Attr
sidenoteAttr = ("",["sidenote"],[])

processNote :: Inline -> Inline
processNote (Note (Para ((Str ss:is)):bs)) = Span sidenoteAttr (breakInlines $ Para ((Str $ T.tail ss):is):bs)
processNote i = i

rawHead :: Int -> Inline
rawHead n = RawInline "html" $ T.concat ["<label for=\"sn", T.pack $ show n, "\" class=\"margin-toggle sidenote-number\"></label>"
                                , "<input type=\"checkbox\" id=\"sn", T.pack $ show n, "\" class=\"margin-toggle\"/>"]
