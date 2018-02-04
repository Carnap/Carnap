module Filter.ProofCheckers (makeProofChecker,splitIt, intoChunks,formatChunk) where

import Text.Pandoc
import Data.List.Split (splitOn)
import Data.Map (unions, fromList, toList)
import Data.Char (isDigit)
import Prelude

makeProofChecker :: Block -> Block
makeProofChecker cb@(CodeBlock (_,classes,extra) contents)
    | "ProofChecker" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | "Playground" `elem` classes = Div ("",[],[]) [toPlayground contents]
    | otherwise = cb
makeProofChecker x = x

activate cls extra chunk
    | "Prop"             `elem` cls = actTemplate [("system","prop")]
    | "FirstOrder"       `elem` cls = actTemplate [("system","firstOrder")]
    | "SecondOrder"      `elem` cls = actTemplate [("system", "secondOrder")]
    | "PolySecondOrder"  `elem` cls = actTemplate [("system", "polyadicSecondOrder")]
    | "LogicBook"        `elem` cls = actTemplate [("system", "LogicBook")]
    | "ForallxSL"        `elem` cls = actTemplate [("system", "magnusSL"), ("options","render")]
    | "ForallxSLPlus"    `elem` cls = actTemplate [("system", "magnusSLPlus"), ("options","render")]
    | "ForallxQL"        `elem` cls = actTemplate [("system", "magnusQL"), ("options","render")]
    | "ZachTFL"          `elem` cls = actTemplate [("system", "thomasBolducAndZachTFL"), ("options","render")]
    | "ZachFOL"          `elem` cls = actTemplate [("system", "thomasBolducAndZachFOL"), ("options","render")]
    | "HardegreeSL"      `elem` cls = actTemplate [("system", "hardegreeSL"),  ("options", "render")]
    | "HardegreePL"      `elem` cls = actTemplate [("system", "hardegreePL"),  ("options", "render")]
    | "HardegreeWTL"     `elem` cls = actTemplate [("system", "hardegreeWTL"), ("options", "render guides fonts")]
    | "HardegreeL"       `elem` cls = actTemplate [("system", "hardegreeL"),   ("options", "guides fonts")]
    | "HardegreeK"       `elem` cls = actTemplate [("system", "hardegreeK"),   ("options", "guides fonts")]
    | "HardegreeT"       `elem` cls = actTemplate [("system", "hardegreeT"),   ("options", "guides fonts")]
    | "HardegreeB"       `elem` cls = actTemplate [("system", "hardegreeB"),   ("options", "guides fonts")]
    | "HardegreeD"       `elem` cls = actTemplate [("system", "hardegreeD"),   ("options", "guides fonts")]
    | "Hardegree4"       `elem` cls = actTemplate [("system", "hardegree4"),   ("options", "guides fonts")]
    | "Hardegree5"       `elem` cls = actTemplate [("system", "hardegree5"),   ("options", "guides fonts")]
    | "HardegreeMPL"     `elem` cls = actTemplate [("system", "hardegreeMPL"), ("options", "guides fonts")]
    | otherwise = RawBlock "html" "<div>No Matching Logic for Derivation</div>"
    where numof = takeWhile (/= ' ')
          seqof = dropWhile (/= ' ')
          (h:t) = formatChunk chunk
          fixed = [("type","proofchecker"),("goal",seqof h),("submission","saveAs:" ++ numof h)]
          actTemplate opts = RawBlock "html" $ 
                "<div class=\"exercise\">"
                ++ "<span> exercise " ++ numof h ++ "</span>"
                ++ "<div"
                ++ concatMap (\(x,y) -> " data-carnap-" ++ x ++ "=\"" ++ y ++ "\"") (toList $ unions [fromList extra, fromList opts, fromList fixed])
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
                ++ "<span>playground</span>"
                ++ "<div"
                ++ " data-carnap-type=\"proofchecker\""
                ++ " data-carnap-system=\"prop\"" 
                ++ ">"
                ++ "</div></div>"

formatChunk = map cleanProof . lines
    where cleanProof l@ (x:xs) = if x == '|' then dropWhile (\y -> isDigit y || (y == '.')) xs
                                             else l
