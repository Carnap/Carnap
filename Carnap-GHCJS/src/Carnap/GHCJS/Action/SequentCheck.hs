{-# LANGUAGE FlexibleContexts, OverloadedStrings, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Action.SequentCheck (sequentCheckAction) where

import Data.Tree
import Data.Either
import Data.Aeson
import Data.Typeable (Typeable)
import Data.Aeson.Types
import Data.Text.Encoding
import Control.Monad (join)
import Data.ByteString.Lazy (fromStrict)
import qualified Text.Parsec as P (parse, ParseError) 
import Control.Lens (view)
#ifdef __GHCJS__
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
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

sequentCheckAction ::  IO ()
sequentCheckAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initializeCallback checkSequent
               return ()

checkSequent :: Value -> IO Value
checkSequent v = do let Success t = parse parseReply v
                    case toTableau gentzenPropLKCalc t of 
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
    | isRight newNode = Left $ Node Correct (map cleanTree parsedForest)
    | Left n <- newNode = Left n
    where parsedLabel = P.parse (parseSeqOver (tbParseForm calc)) "" l
          parsedRule = if r == "" then pure Nothing else P.parse (Just <$> tbParseRule calc) "" r
          parsedForest = map (toTableau calc) f
          cleanTree (Left fs) = fs
          cleanTree (Right fs) = fmap (const Correct) fs
          newNode = case TableauNode <$> parsedLabel <*> (pure Nothing) <*> parsedRule of
                        Right n -> Right n
                        Left e -> Left (Node (Feedback (show e)) (map cleanTree parsedForest))

toInfo :: TreeFeedback -> Value
toInfo (Node Correct ss) = object [ "info" .= ("Correct" :: String), "forest" .= map toInfo ss]
toInfo (Node (Feedback e) ss) = object [ "info" .= e, "forest" .= map toInfo ss]

#ifdef __GHCJS__

foreign import javascript unsafe "checkSequent_ = $1" initializeCallbackJS :: Callback (payload -> succ -> IO ()) -> IO ()
--TODO: unify with other callback code in SequentCheck

foreign import javascript unsafe "$1($2);" simpleCall :: JSVal -> JSVal -> IO ()

initializeCallback :: (Value -> IO Value) -> IO ()
initializeCallback  f = do theCB <- asyncCallback2 (cb f)
                           initializeCallbackJS theCB
    where cb f payload succ = do (Just raw) <- fromJSVal payload
                                 let (Just val) = decode . fromStrict . encodeUtf8 $ raw
                                 rslt <- f val
                                 rslt' <- toJSVal rslt
                                 simpleCall succ rslt'

#else

initializeCallback :: (Value -> IO Value) -> IO ()
initializeCallback = undefined

#endif
