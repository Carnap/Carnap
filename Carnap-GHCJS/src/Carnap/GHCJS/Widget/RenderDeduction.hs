{-# LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Widget.RenderDeduction (renderDeduction) where

import Lib
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Calculi.NaturalDeduction.Syntax (DeductionLine(..), Deduction(..), depth)
import GHCJS.DOM.Element (setInnerHTML,setAttribute)
import GHCJS.DOM.Node (appendChild)
import GHCJS.DOM.Document (createElement)
import Data.Tree (Tree(..))
import Data.List (intercalate)

deductionToForest n ded@(d:ds) = map toTree chunks
    where chunks = chunkBy n ded
          toTree [x] = Node x []
          toTree (x:xs)  = Node x (deductionToForest (depth $ snd x) xs)
deductionToForest _ [] = []

chunkBy n [] = []
chunkBy n (x:xs)
    | deep x = (x:takeWhile deep xs):chunkBy n (dropWhile deep xs)
    | otherwise = [x]:chunkBy n xs
    where deep x = depth (snd x) > n


--this is for Logic Book proofs
renderTree w = treeToElement asLine asSubproof
    where asLine (n,AssertLine f r _ deps) = do (Just theWrapper) <- createElement w (Just "div")
                                                (Just theLine) <- createElement w (Just "div")
                                                (Just lineNum) <- createElement w (Just "span")
                                                (Just theForm) <- createElement w (Just "span")
                                                (Just theRule) <- createElement w (Just "span")
                                                setInnerHTML lineNum (Just $ show n ++ ".")
                                                setInnerHTML theForm (Just $ show f)
                                                setInnerHTML theRule (Just $ show (head r) ++ " " ++ intercalate ", " (map renderDep deps))
                                                appendChild theLine (Just lineNum)
                                                appendChild theLine (Just theForm)
                                                appendChild theLine (Just theRule)
                                                appendChild theWrapper (Just theLine)
                                                return theWrapper
          asLine (n,SeparatorLine _) = do (Just sl) <- createElement w (Just "div")
                                          return sl
          asLine (n,PartialLine _ _ _) = do (Just sl) <- createElement w (Just "div")
                                            return sl

          asSubproof l ls = do setAttribute l "class" "subproof"
                               mapM_ (appendChild l . Just) ls

renderDep (n,m) = if n==m then show n else show n ++ "-" ++ show m

renderDeduction w ded = do let forest = deductionToForest 0 (zip [1..] ded)
                           lines <- mapM (renderTree w) forest
                           (Just theProof) <- createElement w (Just "div")
                           mapM_ (appendChild theProof . Just) lines
                           return theProof
