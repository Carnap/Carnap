{-# LANGUAGE FlexibleContexts, OverloadedStrings, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Action.SequentCheck (sequentCheckAction) where

import Lib
import Data.Tree
import Data.Either
import Data.Aeson
import Data.Typeable (Typeable)
import Data.Aeson.Types
import Control.Monad (join)
import qualified Text.Parsec as P (parse) 
import Control.Lens (view)
import GHCJS.DOM
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Calculi.Util
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.Tableau.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
import Carnap.Languages.PurePropositional.Logic.Gentzen
import Carnap.Languages.PureFirstOrder.Logic.Gentzen

sequentCheckAction ::  IO ()
sequentCheckAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initCallbackObj
               initializeCallback "checkPropSequent" checkPropSequent
               initializeCallback "checkFOLSequent" checkFOLSequent
               return ()

checkPropSequent :: Value -> IO Value
checkPropSequent v = do let Success t = parse parseReply v
                        case toTableau gentzenPropLKCalc t of 
                            Left feedback -> return . toInfo $ feedback
                            Right tab -> return . toInfo . validateTree $ tab

checkFOLSequent :: Value -> IO Value
checkFOLSequent v = do let Success t = parse parseReply v
                       case toTableau gentzenFOLKCalc t of 
                           Left feedback -> return . toInfo $ feedback
                           Right tab -> return . toInfo . validateTree $ tab

parseReply :: Value -> Parser (Tree (String,String))
parseReply = withObject "Sequent Tableau" $ \o -> do
    thelabel   <- o .: "label" :: Parser String
    therule <- o .: "rule" :: Parser String
    theforest <- o .: "forest" :: Parser [Value]
    filteredForest <- filter (\(Node (x,y) _) -> x /= "") <$> mapM parseReply theforest
    --ignore empty nodes
    return $ Node (thelabel,therule) filteredForest

toTableau :: ( Typeable sem
             , ReLex lex
             , Sequentable lex
             ) => TableauCalc lex sem rule -> Tree (String,String) -> Either TreeFeedback (Tableau lex sem rule)
toTableau calc (Node (l,r) f) 
    | all isRight parsedForest && isRight newNode = Node <$> newNode <*> sequence parsedForest
    | isRight newNode = Left $ Node Waiting (map cleanTree parsedForest)
    | Left n <- newNode = Left n
    where parsedLabel = P.parse (parseSeqOver (tbParseForm calc)) "" l
          parsedRule = if r == "" then pure Nothing else P.parse (Just <$> tbParseRule calc) "" r
          parsedForest = map (toTableau calc) f
          cleanTree (Left fs) = fs
          cleanTree (Right fs) = fmap (const Waiting) fs
          newNode = case TableauNode <$> parsedLabel <*> (pure Nothing) <*> parsedRule of
                        Right n -> Right n
                        Left e -> Left (Node (ParseErrorMsg (show e)) (map cleanTree parsedForest))

toInfo :: TreeFeedback -> Value
toInfo (Node Correct ss) = object [ "info" .= ("Correct" :: String), "class" .= ("correct" :: String), "forest" .= map toInfo ss]
toInfo (Node (Feedback e) ss) = object [ "info" .= e, "class" .= ("feedback" :: String), "forest" .= map toInfo ss]
toInfo (Node Waiting ss) = object [ "info" .= ("Waiting for parsing to be completed." :: String), "class" .= ("waiting" :: String), "forest" .= map toInfo ss]
toInfo (Node (ParseErrorMsg e) ss) = object [ "info" .= e, "class" .= ("parse-error" :: String), "forest" .= map toInfo ss]

