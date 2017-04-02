{-# LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Widget.RenderDeduction (renderDeductionFitch, renderDeductionMontegue) where

import Lib
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Calculi.NaturalDeduction.Syntax (DeductionLine(..), Deduction(..), depth)
import GHCJS.DOM.Types (Document,Element)
import GHCJS.DOM.Element (setInnerHTML,setAttribute)
import GHCJS.DOM.Node (appendChild)
import GHCJS.DOM.Document (createElement)
import Data.Tree (Tree(..))
import Data.List (intercalate)

deductionToForest n ded@(d:ds) = map toTree chunks
    where chunks = chunkBy n ded
          toTree (Left x) = Node x []
          toTree (Right (x:xs)) = Node x (deductionToForest (depth $ snd x) ((0,SeparatorLine 0):xs))
deductionToForest _ [] = []

chunkBy n [] = []
chunkBy n (x:xs)
    | deep x = Right (x:takeWhile deep xs):chunkBy n (dropWhile deep xs)
    | otherwise = Left x:chunkBy n xs
    where deep x = depth (snd x) > n

--this is for Fitch proofs
renderTreeFitch w = treeToElement asLine asSubproof
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

-- TODO DRY this up
--this is for Kalish and Montegue Proofs
renderTreeMontegue w = treeToElement asLine asSubproof
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
                                                setAttribute theRule "class" "rule"
                                                setAttribute theWrapper "class" "assertion"
                                                return theWrapper

          asLine (n,ShowLine f _)   = do (Just theWrapper) <- createElement w (Just "div")
                                         (Just theLine) <- createElement w (Just "div")
                                         (Just lineNum) <- createElement w (Just "span")
                                         (Just theForm) <- createElement w (Just "span")
                                         (Just theHead) <- createElement w (Just "span")
                                         setInnerHTML lineNum (Just $ show n ++ ".")
                                         setInnerHTML theForm (Just $ show f)
                                         setInnerHTML theHead (Just $ "Show: ")
                                         appendChild theLine (Just lineNum)
                                         appendChild theLine (Just theHead)
                                         appendChild theLine (Just theForm)
                                         appendChild theWrapper (Just theLine)
                                         setAttribute theWrapper "class" "show"
                                         return theWrapper

          asLine (n,QedLine r _ deps) = do (Just theWrapper) <- createElement w (Just "div")
                                           (Just theLine) <- createElement w (Just "div")
                                           (Just lineNum) <- createElement w (Just "span")
                                           (Just theRule) <- createElement w (Just "span")
                                           setInnerHTML lineNum (Just $ show n ++ ".")
                                           setInnerHTML theRule (Just $ show (head r) ++ " " ++ intercalate ", " (map renderDep deps))
                                           appendChild theLine (Just lineNum)
                                           appendChild theLine (Just theRule)
                                           appendChild theWrapper (Just theLine)
                                           setAttribute theRule "class" "rule"
                                           setAttribute theWrapper "class" "qed"
                                           return theWrapper

          asLine (n,SeparatorLine _) = do (Just sl) <- createElement w (Just "div")
                                          return sl

          asLine (n,PartialLine _ _ _) = do (Just sl) <- createElement w (Just "div")
                                            return sl

          asSubproof l ls = do setAttribute l "class" "subproof"
                               mapM_ (appendChild l . Just) ls

renderDep (n,m) = if n==m then show n else show n ++ "-" ++ show m

renderDeduction :: String -> (Document -> Tree (Int, DeductionLine t t1 t2) -> IO Element) -> Document -> [DeductionLine t t1 t2] -> IO Element
renderDeduction cls render w ded = 
        do let forest = deductionToForest 0 (zip [1..] ded)
           lines <- mapM (render w) forest
           (Just theProof) <- createElement w (Just "div")
           setAttribute theProof "class" cls
           mapM_ (appendChild theProof . Just) lines
           return theProof

renderDeductionFitch :: (Show t,Schematizable (t1 (FixLang t1)), CopulaSchema (FixLang t1)) => Document -> [DeductionLine t t1 t2] -> IO Element
renderDeductionFitch = renderDeduction "fitchDisplay" renderTreeFitch

renderDeductionMontegue :: (Show t,Schematizable (t1 (FixLang t1)), CopulaSchema (FixLang t1)) => Document -> [DeductionLine t t1 t2] -> IO Element
renderDeductionMontegue = renderDeduction "montegueDisplay" renderTreeMontegue

