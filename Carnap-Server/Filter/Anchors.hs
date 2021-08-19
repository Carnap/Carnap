module Filter.Anchors where

import Import
import Text.Pandoc (Inline(..), Block(..))

-- some code is from https://github.com/jgm/pandoc-website/issues/49

makeAnchors :: Block -> Block
makeAnchors (Header level meta@(identifier, _classes, _kvps) inlines)
            | not . null $ identifier =
    Header level meta inlines'
    where
        link = Link ("", ["anchor":: Text], [("aria-hidden", "true")]) [] ("#" <> identifier, "heading anchor link")
        inlines' = link:inlines
makeAnchors x = x
