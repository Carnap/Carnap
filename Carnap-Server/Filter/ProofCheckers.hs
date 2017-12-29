module Filter.ProofCheckers (makeProofChecker,splitIt, intoChunks,formatChunk) where

import Text.Pandoc
import Data.List.Split (splitOn)
import Data.Char (isDigit)
import Prelude

makeProofChecker :: Block -> Block
makeProofChecker cb@(CodeBlock (_,classes,_) contents)
    | "ProofChecker" `elem` classes = Div ("",[],[]) $ map (activate classes) $ intoChunks contents
    | "Playground" `elem` classes = Div ("",[],[]) [toPlayground contents]
    | otherwise = cb
makeProofChecker x = x

activate cls chunk
    | "Prop" `elem` cls = actTemplate "data-carnap-system=\"prop\""
    | "FirstOrder" `elem` cls = actTemplate "data-carnap-system=\"firstOrder\""
    | "SecondOrder" `elem` cls = actTemplate "data-carnap-system=\"secondOrder\""
    | "PolySecondOrder" `elem` cls = actTemplate "data-carnap-system=\"polyadicSecondOrder\""
    | "LogicBook" `elem` cls = actTemplate "data-carnap-system=\"LogicBook\""
    | "ForallxSL" `elem` cls = actTemplate "data-carnap-system=\"magnusSL\" data-carnap-options=\"render\""
    | "ForallxSLPlus" `elem` cls = actTemplate "data-carnap-system=\"magnusSLPlus\" data-carnap-options=\"render\""
    | "ForallxQL" `elem` cls = actTemplate "data-carnap-system=\"magnusQL\" data-carnap-options=\"render\""
    | "HardegreeSL" `elem` cls = actTemplate "data-carnap-system=\"hardegreeSL\" data-carnap-options=\"render\""
    | "HardegreePL" `elem` cls = actTemplate "data-carnap-system=\"hardegreePL\" data-carnap-options=\"render\""
    | "HardegreeWTL" `elem` cls = actTemplate "data-carnap-system=\"hardegreeWTL\" data-carnap-options=\"render guides fonts\""
    --XXX: Keep render off below until we have nicer rendering of indicies
    | "HardegreeL"   `elem` cls = actTemplate "data-carnap-system=\"hardegreeL\" data-carnap-options=\"guides fonts\"" 
    | "HardegreeK"   `elem` cls = actTemplate "data-carnap-system=\"hardegreeK\" data-carnap-options=\"guides fonts\""
    | "HardegreeT"   `elem` cls = actTemplate "data-carnap-system=\"hardegreeT\" data-carnap-options=\"guides fonts\""
    | "HardegreeB"   `elem` cls = actTemplate "data-carnap-system=\"hardegreeB\" data-carnap-options=\"guides fonts\""
    | "HardegreeD"   `elem` cls = actTemplate "data-carnap-system=\"hardegreeD\" data-carnap-options=\"guides fonts\""
    | "Hardegree4"   `elem` cls = actTemplate "data-carnap-system=\"hardegree4\" data-carnap-options=\"guides fonts\""
    | "Hardegree5"   `elem` cls = actTemplate "data-carnap-system=\"hardegree5\" data-carnap-options=\"guides fonts\""
    | "HardegreeMPL" `elem` cls = actTemplate "data-carnap-system=\"hardegreeMPL\" data-carnap-options=\"guides fonts\""
    | otherwise = RawBlock "html" "<div>No Matching Logic for Derivation</div>"
    where numof = takeWhile (/= ' ')
          seqof = dropWhile (/= ' ')
          (h:t) = formatChunk chunk
          actTemplate opts = RawBlock "html" $ 
                "<div class=\"exercise\">"
                ++ "<span> exercise " ++ numof h ++ "</span>"
                ++ "<div"
                ++ " data-carnap-type=\"proofchecker\" "
                ++ opts 
                ++ " data-carnap-goal=\"" ++ seqof h ++ "\""
                ++ " data-carnap-submission=\"saveAs:" ++ numof h ++ "\""
                ++ ">"
                ++ unlines t 
                ++ "</div></div>"

splitIt [] = ([],[])
splitIt l = case break (== '\n') l of
                (h,t@(_:x:xs)) -> if x == '|'
                                then let (h',t') = splitIt (x:xs) in
                                    (h ++ ('\n':h'),t')
                                else (h,x:xs)
                y -> y

intoChunks [] = []
intoChunks l = cons $ case splitIt l of (h,t) -> (h,intoChunks t)
    where cons (h,t) = h : t

toPlayground contents = RawBlock "html" $
        "<div class=\"exercise\">"
        ++ "<span> playground </span>"
        ++ "<div class=\"proofchecker playground\"><div class = \"goal\"></div>"
        ++ "<textarea>" ++ contents ++ "</textarea><div class=\"output\"></div></div></div>"

formatChunk = map cleanProof . lines
    where cleanProof l@ (x:xs) = if x == '|' then dropWhile (\y -> isDigit y || (y == '.')) xs
                                             else l
