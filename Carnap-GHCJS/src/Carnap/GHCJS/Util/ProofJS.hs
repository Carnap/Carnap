{-# LANGUAGE FlexibleContexts, OverloadedStrings, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Util.ProofJS where

import Lib (cleanString, toJSONString, toCleanVal, keyString)
import Data.Aeson
import Data.Aeson.Types
import Data.Tree
import Control.Monad.IO.Class (liftIO)
import Carnap.Calculi.Util
#ifdef __GHCJS__
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
import GHCJS.Types
import GHCJS.DOM.HTMLElement (setInnerText, getInnerText, castToHTMLElement)
import GHCJS.DOM.Element (setInnerHTML, setAttribute, keyDown, input)
import GHCJS.DOM.Node (appendChild, removeChild, getParentNode, insertBefore, getParentElement)
import GHCJS.DOM.Document (createElement, getActiveElement)
import GHCJS.DOM.EventM
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.Types (Element, toJSString, fromJSString, Document)

initRoot :: String -> Element -> IO JSVal
initRoot s elt = do root <- newRoot s
                    renderOn elt root
                    return root

initMutRoot :: String -> Element -> IO JSVal
initMutRoot s elt = do root <- newMutRoot s
                       renderOn elt root
                       return root

parseTreeJSON :: Value -> Parser (Tree (String,String))
parseTreeJSON = withObject "Sequent Tableau" $ \o -> do
    thelabel   <- o .: "label" :: Parser String
    therule <- o .: "rule" :: Parser String
    theforest <- o .: "forest" :: Parser [Value]
    filteredForest <- filter (\(Node (x,y) _) -> x /= "") <$> mapM parseTreeJSON theforest
    --ignore empty nodes
    return $ Node (thelabel,therule) filteredForest

isEmptyLeaf :: Value -> Bool
isEmptyLeaf v = case parse parser v of
                    Success True -> True
                    _ -> False
    where parser = withObject "Sequent Tableau" $ \o -> do
                      thelabel   <- o .: "label" :: Parser String
                      therule <- o .: "rule" :: Parser String
                      theforest <- o .: "forest" :: Parser [Value]
                      return $ null thelabel && null therule && null theforest 

blankInfo :: Value
blankInfo = object [ "info" .= ("" :: String), "class" .= ("" :: String), "forest" .= ([] :: [Value]) ]

toInfo :: TreeFeedback lex -> Value
toInfo (Node Correct ss) = object [ "info" .= ("Correct" :: String), "class" .= ("correct" :: String), "forest" .= map toInfo ss]
toInfo (Node (ProofData s) ss) = object [ "info" .= s, "class" .= ("correct" :: String), "forest" .= map toInfo ss]
toInfo (Node Waiting ss) = object [ "info" .= ("Waiting for parsing to be completed." :: String), "class" .= ("waiting" :: String), "forest" .= map toInfo ss]
toInfo (Node (ProofError (NoParse e _)) ss) = object [ "info" .= cleanString (show e), "class" .= ("parse-error" :: String), "forest" .= map toInfo ss]
toInfo (Node (ProofError (GenericError s _)) ss) = object [ "info" .= s, "class" .= ("feedback" :: String), "forest" .= map toInfo ss]
--TODO: actually display unification feedback
toInfo (Node (ProofError (NoUnify eqs _)) ss) = object [ "info" .= ("This doesn't follow by this rule" :: String), "class" .= ("feedback" :: String), "forest" .= map toInfo ss]
toInfo (Node (ProofError (NoResult _)) ss) = object [ "info" .= ("" :: String) , "class" .= ("correct" :: String), "forest" .= map toInfo ss]

fromInfo :: Value -> Parser (Maybe Bool)
fromInfo = withObject "Info Tree" $ \o -> do
    theInfo <- o .: "class" :: Parser String
    theForest <- o .: "forest" :: Parser [Value]
    processedForest <- mapM fromInfo theForest
    return $ case theInfo of
        "correct" -> foldl (\x y -> (&&) <$> x <*> y) (Just True) processedForest
        "" | null theForest-> foldl (\x y -> (&&) <$> x <*> y) (Just True) processedForest
        "" -> Nothing --a global edit must have occured
        _ -> Just False

checkFullInfo :: Value -> IO Value
checkFullInfo v = do let Success t = parse fromInfo v
                     case t of
                         Just True -> return $ object [ "result" .= ("yes" :: String)]
                         _ -> return $ object [ "result" .= ("no" :: String)]

attachDisplay :: Document -> Element -> JSVal -> IO ()
attachDisplay w elt root = do
          Just displayDiv <- createElement w (Just ("div" :: String))
          setAttribute displayDiv ("class" :: String) ("jsonDisplay" :: String)
          setAttribute displayDiv ("contenteditable" :: String) ("true" :: String)
          val <- toCleanVal root
          setInnerText (castToHTMLElement displayDiv) . Just $ toJSONString val
          toggleDisplay <- newListener $ do
              kbe <- event
              isCtrl <- getCtrlKey kbe
              isShift <- getShiftKey kbe
              code <- liftIO $ keyString kbe
              liftIO $ print code
              if (isCtrl && code == "?") || (isCtrl && isShift && code == "/")
                  then do
                      preventDefault
                      mparent <- getParentNode displayDiv
                      case mparent of
                          Just p -> removeChild elt (Just displayDiv)
                          _ -> appendChild elt (Just displayDiv)
                      return ()
                  else return ()
          addListener elt keyDown toggleDisplay False
          updateRoot <- newListener $ liftIO $ do 
                Just json <- getInnerText (castToHTMLElement displayDiv)
                replaceRoot root json
          addListener displayDiv input updateRoot False
          root `onChange` (\_ -> do
                   mfocus <- getActiveElement w
                   --don't update when the display is
                   --focussed, to avoid cursor jumping
                   if Just displayDiv /= mfocus then do
                       val <- toCleanVal root
                       setInnerText (castToHTMLElement displayDiv) . Just $ toJSONString val
                   else return ())
          return ()


#ifdef __GHCJS__

foreign import javascript unsafe "(function(){root = new ProofRoot(JSON.parse($1)); return root})()" newRootJS :: JSString-> IO JSVal

foreign import javascript unsafe "(function(){root = new DeductionRoot(JSON.parse($1)); return root})()" newMutRootJS :: JSString-> IO JSVal

foreign import javascript unsafe "(function(){$2.renderOn($1); $1.proofRoot = $2})()" renderOnJS :: Element -> JSVal -> IO ()

foreign import javascript unsafe "$1.decorate($2)" decorateJS :: JSVal -> JSVal -> IO ()

foreign import javascript unsafe "$1.toInfo()" valToInfo :: JSVal -> IO JSVal

foreign import javascript unsafe "$1.label" rootLabelJS :: JSVal -> IO JSString

foreign import javascript unsafe "$1.on('changed',$2)" onChangeJS :: JSVal -> Callback(JSVal -> IO ()) -> IO ()

foreign import javascript unsafe "(function() {var rslt; if ($1.parentNode) {rslt=$1.parentNode} else {rslt=$1}; return rslt})()" ascendTree :: JSVal -> IO JSVal

foreign import javascript unsafe "try {$1.replace(JSON.parse($2))} catch(e) {console.log(e)};" replaceRoot :: JSVal -> JSString -> IO ()

newRoot :: String -> IO JSVal
newRoot s = newRootJS (toJSString s)

newMutRoot :: String -> IO JSVal
newMutRoot s = newMutRootJS (toJSString s)

renderOn :: Element -> JSVal -> IO ()
renderOn elt root = renderOnJS elt root

getRootLabel :: JSVal -> IO String
getRootLabel root = fromJSString <$> rootLabelJS root

onChange :: JSVal -> (JSVal -> IO ()) -> IO ()
onChange val f = asyncCallback1 f >>= onChangeJS val 

decorate :: JSVal -> Value -> IO ()
decorate x v = toJSVal v >>= decorateJS x

#else

newRoot s = error "you need the JavaScript FFI to call newRoot"

newMutRoot s = error "you need the JavaScript FFI to call newMutRoot"

renderOn :: Element -> JSVal -> IO ()
renderOn = error "you need the JavaScript FFI to call renderOn"

onChange :: JSVal -> (JSVal -> IO ()) -> IO ()
onChange = error "you need the JavaScript FFI to call onChange"

decorate :: JSVal -> Value -> IO ()
decorate = error "you need the JavaScript FFI to call decorate"

ascendTree :: JSVal -> IO JSVal
ascendTree = error "you need the JavaScript FFI to call ascendTree"

valToInfo :: JSVal -> IO JSVal
valToInfo = error "you need the JavaScript FFI to call valToInfo"

replaceRoot :: JSVal -> JSString -> IO ()
replaceRoot = error "you need the JavaScript FFI to call replaceRoot"

#endif
