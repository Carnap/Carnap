{-# LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Widget.RenderDeduction (renderDeductionFitch, renderDeductionMontague, renderDeductionLemmon, renderNull) where

import Lib
import Data.Maybe (catMaybes)
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.GHCJS.Widget.ProofCheckBox
import Carnap.Calculi.NaturalDeduction.Syntax 
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
renderTreeFitch ded w calc = treeToElement asLine asSubproof
    where asLine (n,AssertLine f r _ deps) = do (theWrapper,theLine,theForm,theRule) <- if n == finalPrem
                                                                                            then lineBase w calc n (Just f) (Just (r,deps)) "final-premise"
                                                                                            else lineBase w calc n (Just f) (Just (r,deps)) "assertion"
                                                appendChild theLine (Just theForm)
                                                appendChild theLine (Just theRule)
                                                return theWrapper

          asLine _ = do (Just sl) <- createElement w (Just "div")
                        return sl

          asSubproof l ls = do setAttribute l "class" "subproof"
                               mapM_ (appendChild l . Just) ls
          finalPrem = length (takeWhile (\d -> isPremiseLine d && depth d == 0) ded)

--this is for Kalish and Montague Proofs
renderTreeMontague w calc = treeToElement asLine asSubproof
    where asLine (n,AssertLine f r _ deps) = do (theWrapper,theLine,theForm,theRule) <- lineBase w calc n (Just f) (Just (r,deps)) "assertion"
                                                appendChild theLine (Just theForm)
                                                appendChild theLine (Just theRule)
                                                return theWrapper

          asLine (n,ShowWithLine f _ r deps) = do (theWrapper,theLine,theForm,theRule) <- lineBase w calc n (Just f) (Just (r,deps)) "show"
                                                  (Just theHead) <- createElement w (Just "span")
                                                  setInnerHTML theHead (Just $ "Show: ")
                                                  appendChild theLine (Just theHead)
                                                  appendChild theLine (Just theForm)
                                                  appendChild theLine (Just theRule)
                                                  return theWrapper

          asLine (n,ShowLine f _)   = do (theWrapper,theLine,theForm,_) <- lineBase w calc n (Just f) norule "show"
                                         (Just theHead) <- createElement w (Just "span")
                                         setInnerHTML theHead (Just $ "Show: ")
                                         appendChild theLine (Just theHead)
                                         appendChild theLine (Just theForm)
                                         return theWrapper

          asLine (n,QedLine r _ deps) = do (theWrapper,theLine,_,theRule) <- lineBase w calc n noform (Just (r,deps)) "qed"
                                           appendChild theLine (Just theRule)
                                           --appendChild theWrapper (Just theLine)
                                           return theWrapper

          asLine _ = do (Just sl) <- createElement w (Just "div")
                        return sl

          asSubproof l ls = do setAttribute l "class" "subproof"
                               mapM_ (appendChild l . Just) ls

          noform :: Maybe ()
          noform = Nothing

          norule :: Maybe ([()],[(Int,Int)])
          norule = Nothing

--The basic parts of a line, with Maybes for the fomula and the rule-dependency pair.
-- lineBase :: (Show a, Show b) => 
--     Document -> CheckerOptions -> Int -> Maybe a -> Maybe ([b],[(Int,Int)]) -> String -> IO (Element,Element,Element,Element)
lineBase w calc n mf mrd lineclass = 
        do (Just theWrapper) <- createElement w (Just "div")
           (Just theLine) <- createElement w (Just "div")
           (Just lineNum) <- createElement w (Just "span")
           (Just theForm) <- createElement w (Just "span")
           (Just theRule) <- createElement w (Just "span")
           setInnerHTML lineNum (Just $ show n ++ ".")
           let ruleString r deps = case ndRenderer calc of
                   FitchStyle BergmanMooreAndNelsonStyle -> intercalate ", " (map renderDep deps) ++ " " ++ show (head r)
                   _ -> show (head r) ++ " " ++ intercalate ", " (map renderDep deps)
           whileJust mrd (\(r,deps) -> setInnerHTML theRule (Just $ ruleString r deps))
           whileJust mf (\f -> setInnerHTML theForm (Just $ ndNotation calc $ show f))
           setAttribute theRule "class" "rule"
           appendChild theWrapper (Just theLine)
           appendChild theLine (Just lineNum)
           setAttribute theWrapper "class" lineclass
           return (theWrapper,theLine,theForm,theRule)

renderTreeLemmon w calc = treeToElement asLine asSubproof
    where asLine (n,l@(DependentAssertLine f r deps _ scope mnum)) = 
                do [theWrapper,lineNum,theForm,theRule,theScope] <- catMaybes <$> mapM (createElement w . Just) ["div","span","span","span","span"]
                   case ndRenderer calc of
                       LemmonStyle TomassiStyle -> 
                            do setInnerHTML theScope (Just $ "{" ++ intercalate "," (map show scope) ++ "}")
                               setInnerHTML theForm (Just $ ndNotation calc $ show f)
                               case mnum of
                                   Nothing -> setInnerHTML lineNum (Just $ show n ++ ".")
                                   Just m -> setInnerHTML lineNum (Just $ show m ++ ".")
                       _ -> do setInnerHTML theScope (Just $ show scope)
                               setInnerHTML theForm (Just $ ndNotation calc $ show f)
                               case mnum of
                                   Nothing -> setInnerHTML lineNum (Just $ "(" ++ show n ++ ")")
                                   Just m -> setInnerHTML lineNum (Just $ "(" ++ show m ++ ")")
                   setAttribute theRule "class" "rule"
                   setInnerHTML theRule (Just $ show (head r) ++ showdischarged ++ showdeps)
                   mapM (appendChild theWrapper. Just) [theScope,lineNum,theForm,theRule]
                   return theWrapper
                   
                where showdischarged = if discharged l /= [] then show (discharged l) else ""

                      showdeps = if deps /= [] then "(" ++ intercalate "," (map renderDep deps) ++ ")" else "" 

          asLine _ = do Just sl <- createElement w (Just "div")
                        return sl

          asSubproof _ _ = return ()

renderDeduction :: String -> (Document -> NaturalDeductionCalc r lex sem -> Tree (Int, DeductionLine t t1 t2) -> IO Element) -> Document -> NaturalDeductionCalc r lex sem -> [DeductionLine t t1 t2] -> IO Element
renderDeduction cls render w calc ded = 
        do let forest = deductionToForest 0 (zip [1..] ded)
           lines <- mapM (render w calc) forest
           (Just theProof) <- createElement w (Just "div")
           setAttribute theProof "class" cls
           mapM_ (appendChild theProof . Just) lines
           return theProof

renderDeductionFitch :: (Show r,Schematizable (lex (FixLang lex)), CopulaSchema (FixLang lex), Inference r lex sem) => 
    Document -> NaturalDeductionCalc r lex sem -> [DeductionLine r lex sem] -> IO Element
renderDeductionFitch w calc ded = renderDeduction "fitchDisplay" (renderTreeFitch ded) w calc ded

renderDeductionMontague :: (Show r,Schematizable (lex (FixLang lex)), CopulaSchema (FixLang lex)) => 
    Document -> NaturalDeductionCalc r lex sem -> [DeductionLine r lex sem] -> IO Element
renderDeductionMontague = renderDeduction "montagueDisplay" renderTreeMontague

renderDeductionLemmon ::  (Show t,Schematizable (t1 (FixLang t1)), CopulaSchema (FixLang t1)) => 
    Document -> NaturalDeductionCalc r lex sem -> [DeductionLine t t1 t2] -> IO Element
renderDeductionLemmon = renderDeduction "lemmonDisplay" renderTreeLemmon

renderNull :: Document -> NaturalDeductionCalc r lex sem -> [DeductionLine t t1 t2] -> IO Element
renderNull w _ _ = do Just e <- createElement w (Just "div")
                      return e

renderDep (n,m) = if n==m then show n else show n ++ "-" ++ show m

whileJust :: Monad m => Maybe a -> (a -> m b) -> m ()
whileJust (Just m) f = f m >> return ()
whileJust Nothing _ = return ()
