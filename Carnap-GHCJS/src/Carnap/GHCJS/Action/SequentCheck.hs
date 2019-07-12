{-# LANGUAGE OverloadedStrings, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Action.SequentCheck (sequentCheckAction) where

import Data.Tree
import Data.Aeson
import Data.Aeson.Types
import Data.Text.Encoding
import Data.ByteString.Lazy (fromStrict)
#ifdef __GHCJS__
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
import GHCJS.DOM

sequentCheckAction ::  IO ()
sequentCheckAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initializeCallback checkSequent
               return ()

checkSequent :: Value -> IO Value
checkSequent v = do let Success t = parse parseReply v
                    print t
                    return v

parseReply :: Value -> Parser (Tree (String,String))
parseReply = withObject "Sequent Tableau" $ \o -> do
    thelabel   <- o .: "label" :: Parser String
    therule <- o .: "rule" :: Parser String
    theforest <- o .: "forest" :: Parser [Value]
    Node (thelabel,therule) <$>  mapM parseReply theforest

#ifdef __GHCJS__

foreign import javascript unsafe "checkSequent_ = $2" initializeCallbackJS :: Callback (payload -> succ -> IO ()) -> IO ()
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
