module Filter.ProofCheckers (makeProofChecker) where

import Text.Pandoc
import Data.List.Split (splitOn)
import Data.Map (Map, unions, fromList, toList)
import Filter.Util (splitIt, intoChunks,formatChunk,unlines')
import Prelude

makeProofChecker :: Block -> Block
makeProofChecker cb@(CodeBlock (_,classes,extra) contents)
    | "ProofChecker" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | "Playground" `elem` classes = Div ("",[],[]) [toPlayground classes extra contents]
    | otherwise = cb
makeProofChecker x = x

activate cls extra chunk
    | "Prop"             `elem` cls = exTemplate [("system", "prop"),("guides","montague"),("options","resize")]
    | "FirstOrder"       `elem` cls = exTemplate [("system", "firstOrder"),("guides","montague"),("options","resize")]
    | "SecondOrder"      `elem` cls = exTemplate [("system", "secondOrder")]
    | "PolySecondOrder"  `elem` cls = exTemplate [("system", "polyadicSecondOrder")]
    | "ElementaryST"     `elem` cls = exTemplate [("system", "elementarySetTheory"),("options","resize render")]
    | "SeparativeST"     `elem` cls = exTemplate [("system", "separativeSetTheory"),("options","resize render")]
    | "MontagueSC"       `elem` cls = exTemplate [("system", "montagueSC"),("options","resize")]
    | "MontagueQC"       `elem` cls = exTemplate [("system", "montagueQC"),("options","resize")]
    | "LogicBookSD"      `elem` cls = exTemplate [("system", "LogicBookSD")]
    | "LogicBookSDPlus"  `elem` cls = exTemplate [("system", "LogicBookSDPlus")]
    | "LogicBookPD"      `elem` cls = exTemplate [("system", "LogicBookPD")]
    | "LogicBookPDPlus"  `elem` cls = exTemplate [("system", "LogicBookPDPlus")]
    | "HausmanSL"        `elem` cls = exTemplate [("system", "hausmanSL"), ("guides","hausman"), ("options", "resize fonts") ]
    | "HausmanPL"        `elem` cls = exTemplate [("system", "hausmanPL"), ("guides","hausman"), ("options", "resize fonts") ]
    | "HowardSnyderSL"   `elem` cls = exTemplate [("system", "howardSnyderSL"), ("guides","howardSnyder"), ("options", "resize fonts") ]
    | "HowardSnyderPL"   `elem` cls = exTemplate [("system", "howardSnyderPL"), ("guides","howardSnyder"), ("options", "resize fonts") ]
    | "ForallxSL"        `elem` cls = exTemplate [("system", "magnusSL"), ("options","render")]
    | "ForallxSLPlus"    `elem` cls = exTemplate [("system", "magnusSLPlus"), ("options","render")]
    | "ForallxQL"        `elem` cls = exTemplate [("system", "magnusQL"), ("options","render")]
    | "IchikawaJenkinsSL"`elem` cls = exTemplate [("system", "ichikawaJenkinsSL"), ("options","render")]
    | "IchikawaJenkinsQL"`elem` cls = exTemplate [("system", "ichikawaJenkinsQL"), ("options","render")]
    | "TomassiPL"        `elem` cls = exTemplate [("system", "tomassiPL"), ("options","resize render hideNumbering")]
    | "GoldfarbND"       `elem` cls = exTemplate [("system", "goldfarbND")]
    | "GoldfarbAltND"    `elem` cls = exTemplate [("system", "goldfarbAltND")]
    | "GoldfarbNDPlus"   `elem` cls = exTemplate [("system", "goldfarbNDPlus")]
    | "GoldfarbAltNDPlus"`elem` cls = exTemplate [("system", "goldfarbAltNDPlus")]
    | "ZachTFL"          `elem` cls = exTemplate [("system", "thomasBolducAndZachTFL"), ("options","render")]
    | "ZachFOL"          `elem` cls = exTemplate [("system", "thomasBolducAndZachFOL"), ("options","render")]
    | "HardegreeSL"      `elem` cls = exTemplate [("system", "hardegreeSL"),  ("options", "render")]
    | "HardegreePL"      `elem` cls = exTemplate [("system", "hardegreePL"),  ("options", "render")]
    | "HardegreeWTL"     `elem` cls = exTemplate [("system", "hardegreeWTL"), ("guides", "montague"), ("options", "render fonts")]
    | "HardegreeL"       `elem` cls = exTemplate [("system", "hardegreeL"), ("guides", "montague"),   ("options", "fonts")]
    | "HardegreeK"       `elem` cls = exTemplate [("system", "hardegreeK"), ("guides", "montague"),   ("options", "fonts")]
    | "HardegreeT"       `elem` cls = exTemplate [("system", "hardegreeT"), ("guides", "montague"),   ("options", "fonts")]
    | "HardegreeB"       `elem` cls = exTemplate [("system", "hardegreeB"), ("guides", "montague"),   ("options", "fonts")]
    | "HardegreeD"       `elem` cls = exTemplate [("system", "hardegreeD"), ("guides", "montague"),   ("options", "fonts")]
    | "Hardegree4"       `elem` cls = exTemplate [("system", "hardegree4"), ("guides", "montague"),   ("options", "fonts")]
    | "Hardegree5"       `elem` cls = exTemplate [("system", "hardegree5"), ("guides", "montague"),   ("options", "fonts")]
    | "HardegreeMPL"     `elem` cls = exTemplate [("system", "hardegreeMPL"), ("guides", "montague"), ("options", "fonts")]
    | otherwise = exTemplate []
    where numof = takeWhile (/= ' ')
          seqof = dropWhile (/= ' ')
          (h:t) = formatChunk chunk
          fixed = [("type","proofchecker"),("goal",seqof h),("submission","saveAs:" ++ numof h)]
          exTemplate opts = actTemplate (unions [fromList extra, fromList opts, fromList fixed]) ("exercise " ++ numof h) (unlines' t)

toPlayground cls extra content
    | "Prop"             `elem` cls = playTemplate [("system", "prop")]
    | "FirstOrder"       `elem` cls = playTemplate [("system", "firstOrder")]
    | "SecondOrder"      `elem` cls = playTemplate [("system", "secondOrder")]
    | "PolySecondOrder"  `elem` cls = playTemplate [("system", "polyadicSecondOrder")]
    | "ElementaryST"     `elem` cls = playTemplate [("system", "elementarySetTheory"), ("options","resize render")]
    | "SeparativeST"     `elem` cls = playTemplate [("system", "separativeSetTheory"), ("options","resize render")]
    | "MontagueSC"       `elem` cls = playTemplate [("system", "montagueSC"),("options","resize")]
    | "MontagueQC"       `elem` cls = playTemplate [("system", "montagueQC"),("options","resize")]
    | "LogicBookSD"      `elem` cls = playTemplate [("system", "LogicBookSD")]
    | "LogicBookSDPlus"  `elem` cls = playTemplate [("system", "LogicBookSDPlus")]
    | "LogicBookPD"      `elem` cls = playTemplate [("system", "LogicBookPD")]
    | "LogicBookPDPlus"  `elem` cls = playTemplate [("system", "LogicBookPDPlus")]
    | "HausmanSL"        `elem` cls = playTemplate [("system", "hausmanSL"), ("guides","hausman"), ("options","fonts resize")]
    | "HausmanPL"        `elem` cls = playTemplate [("system", "hausmanPL"), ("guides","hausman"), ("options","fonts resize")]
    | "HowardSnyderSL"   `elem` cls = playTemplate [("system", "howardSnyderSL"), ("guides","howardSnyder"), ("options","fonts resize")]
    | "HowardSnyderPL"   `elem` cls = playTemplate [("system", "howardSnyderPL"), ("guides","howardSnyder"), ("options","fonts resize")]
    | "ForallxSL"        `elem` cls = playTemplate [("system", "magnusSL"), ("options","render")]
    | "ForallxSLPlus"    `elem` cls = playTemplate [("system", "magnusSLPlus"), ("options","render")]
    | "ForallxQL"        `elem` cls = playTemplate [("system", "magnusQL"), ("options","render")]
    | "IchikawaJenkinsSL"`elem` cls = playTemplate [("system", "ichikawaJenkinsSL"), ("options","render")]
    | "IchikawaJenkinsQL"`elem` cls = playTemplate [("system", "ichikawaJenkinsQL"), ("options","render")]
    | "TomassiPL"        `elem` cls = playTemplate [("system", "tomassiPL"), ("options","resize render hideNumbering")]
    | "GoldfarbND"       `elem` cls = playTemplate [("system", "goldfarbND"),("options","resize")]
    | "GoldfarbAltND"    `elem` cls = playTemplate [("system", "goldfarbAltND"),("options","resize")]
    | "GoldfarbNDPlus"   `elem` cls = playTemplate [("system", "goldfarbNDPlus"),("options","resize")]
    | "GoldfarbAltNDPlus"`elem` cls = playTemplate [("system", "goldfarbAltNDPlus"),("options","resize")]
    | "ZachTFL"          `elem` cls = playTemplate [("system", "thomasBolducAndZachTFL"), ("options","render")]
    | "ZachFOL"          `elem` cls = playTemplate [("system", "thomasBolducAndZachFOL"), ("options","render")]
    | "HardegreeSL"      `elem` cls = playTemplate [("system", "hardegreeSL"),  ("options", "render")]
    | "HardegreePL"      `elem` cls = playTemplate [("system", "hardegreePL"),  ("options", "render")]
    | "HardegreeWTL"     `elem` cls = playTemplate [("system", "hardegreeWTL"), ("guides", "montague"), ("options", "render fonts")]
    | "HardegreeL"       `elem` cls = playTemplate [("system", "hardegreeL"),  ("guides", "montague"), ("options", "fonts")]
    | "HardegreeK"       `elem` cls = playTemplate [("system", "hardegreeK"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeT"       `elem` cls = playTemplate [("system", "hardegreeT"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeB"       `elem` cls = playTemplate [("system", "hardegreeB"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeD"       `elem` cls = playTemplate [("system", "hardegreeD"), ("guides", "montague"), ("options", "fonts")]
    | "Hardegree4"       `elem` cls = playTemplate [("system", "hardegree4"), ("guides", "montague"), ("options", "fonts")]
    | "Hardegree5"       `elem` cls = playTemplate [("system", "hardegree5"), ("guides", "montague"), ("options", "fonts")]
    | "HardegreeMPL"     `elem` cls = playTemplate [("system", "hardegreeMPL"), ("guides", "montague"), ("options", "fonts")]
    | otherwise = playTemplate []
    where fixed = [("type","proofchecker")]
          playTemplate opts = actTemplate (unions [fromList extra, fromList opts, fromList fixed]) "Playground" (unlines' $ formatChunk content)

actTemplate :: Map String String -> String -> String -> Block
actTemplate opts head content = Div ("",["exercise"],[])
    [ Plain 
        [Span ("",[],[]) 
            [Str head]
        ]
    , Div ("",[],map (\(x,y) -> ("data-carnap-" ++ x,y)) $ toList opts) 
        [Plain [Str content]]
    ]

