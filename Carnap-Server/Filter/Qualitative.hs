module Filter.Qualitative (makeQualitativeProblems) where

import Carnap.GHCJS.SharedFunctions (simpleHash, simpleCipher)
import Text.Pandoc
import Filter.Util (splitIt, intoChunks,formatChunk, unlines', exerciseWrapper, sanatizeHtml)
import Data.Map (fromList, toList, unions)
import Data.List.Split (splitOn)
import Prelude

makeQualitativeProblems :: Block -> Block
makeQualitativeProblems cb@(CodeBlock (_,classes,extra) contents)
    | "QualitativeProblem" `elem` classes = Div ("",[],[]) $ map (activate classes extra) $ intoChunks contents
    | otherwise = cb
makeQualitativeProblems x = x

activate cls extra chunk
    | "MultipleChoice" `elem` cls = mctemplate (opts [("qualitativetype","multiplechoice"), ("goal", contentOf h) ])
    | "ShortAnswer" `elem` cls = template (opts [("qualitativetype","shortanswer"), ("goal", contentOf h) ])
    | "Numerical" `elem` cls = case splitOn ":" (contentOf h) of
                                   [g,p] -> template (opts [ ("qualitativetype","numerical")
                                                            , ("goal", show (simpleCipher g)) 
                                                            , ("problem", sanatizeHtml p)
                                                            ])
                                   _ -> Div ("",[],[]) [Plain [Str "problem with numerical qualitative problem specification"]]
    | otherwise = RawBlock "html" "<div>No Matching Qualitative Problem Type</div>"
    where numof x = takeWhile (/= ' ') x
          contentOf x = sanatizeHtml . dropWhile (== ' ') . dropWhile (/= ' ') $  x
          (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","qualitative")
                  , ("submission", "saveAs:" ++ numof h)
                  ]
          mctemplate opts = exerciseWrapper (numof h) $
                              --Need rawblock here to get the linebreaks
                              --right.
                              RawBlock "html" 
                                 $ "<div" ++ optString ++ ">" 
                                ++ unlines' (map (show . withHash) t)
                                ++ "</div>"
                where optString = concatMap (\(x,y) -> " data-carnap-" ++ x ++ "=\"" ++ y ++ "\"") (toList opts)
          template opts = exerciseWrapper (numof h) $
                              --Need rawblock here to get the linebreaks
                              --right.
                              RawBlock "html" 
                                 $ "<div" ++ optString ++ ">" 
                                ++ unlines' t
                                ++ "</div>"
                where optString = concatMap (\(x,y) -> " data-carnap-" ++ x ++ "=\"" ++ y ++ "\"") (toList opts)
          withHash s | length s' > 0 = if head s' `elem` ['*','+','-'] then (simpleHash s', tail s') else (simpleHash s',s')
                     | otherwise = (simpleHash s', s')
            where s' = (dropWhile (== ' ') s)
