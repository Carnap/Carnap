module Filter.Sequent (makeSequent) where

import Text.Pandoc
import Data.Map (fromList, toList, unions)
import Prelude

makeSequent :: Block -> Block
makeSequent cb@(CodeBlock (_,classes,extra) contents)
    | "Sequent" `elem` classes = Div ("",[],[]) $ map (activate classes extra) (lines contents)
    | otherwise = cb
makeSequent x = x

activate cls extra cnt
    | "propLK" `elem` cls = template (opts [("system","propLK")])
    | "propLJ" `elem` cls = template (opts [("system","propLJ")])
    | "foLK" `elem` cls = template (opts [("system","foLK")])
    | "foLJ" `elem` cls = template (opts [("system","foLJ")])
    | otherwise = RawBlock "html" "<div>No Matching Sequent Calculus</div>"
    where numof x = takeWhile (/= ' ') x
          propof x = dropWhile (== ' ') . dropWhile (/= ' ') $ x
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("goal", propof cnt) 
                  , ("submission", "saveAs:" ++ numof cnt)
                  , ("type", "sequentchecker")
                  ]
          template opts = Div ("",["exercise"],[])
                            [ Plain 
                                [Span ("",[],[]) 
                                    [Str (numof cnt)]
                                ]
                            , Div ("",[],map (\(x,y) -> ("data-carnap-" ++ x,y)) $ toList opts) []
                            ]
