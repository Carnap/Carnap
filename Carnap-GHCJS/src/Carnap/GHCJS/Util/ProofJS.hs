{-# LANGUAGE FlexibleContexts, OverloadedStrings, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Util.ProofJS where

import Data.Aeson
import Data.Aeson.Types
import Data.Tree
#ifdef __GHCJS__
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
import GHCJS.Types
import GHCJS.DOM.Types (Element, toJSString)

initRoot :: String -> Element -> IO JSVal
initRoot s elt = do root <- newRoot s
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

#ifdef __GHCJS__

foreign import javascript unsafe "(function(){root = new ProofRoot(JSON.parse($1)); return root})()" newRootJS :: JSString-> IO JSVal

foreign import javascript unsafe "$2.renderOn($1)" renderOnJS :: Element -> JSVal -> IO ()

foreign import javascript unsafe "$1.decorate($2)" decorateJS :: JSVal -> JSVal -> IO ()

foreign import javascript unsafe "$1.on('changed',$2)" onChangeJS :: JSVal -> Callback(JSVal -> IO ()) -> IO ()

foreign import javascript unsafe "(function() {var rslt; if ($1.parentNode) {rslt=$1.parentNode} else {rslt=$1}; return rslt})()" ascendTree :: JSVal -> IO JSVal

newRoot :: String -> IO JSVal
newRoot s = newRootJS (toJSString s)

renderOn :: Element -> JSVal -> IO ()
renderOn elt root = renderOnJS elt root

onChange :: JSVal -> (JSVal -> IO ()) -> IO ()
onChange val f = asyncCallback1 f >>= onChangeJS val 

decorate :: JSVal -> Value -> IO ()
decorate x v = toJSVal v >>= decorateJS x

#else

newRoot s = error "you need the JavaScript FFI to call newRoot"

renderOn :: Element -> JSVal -> IO ()
renderOn = error "you need the JavaScript FFI to call renderOn"

onChange :: JSVal -> (JSVal -> IO ()) -> IO ()
onChange = error "you need the JavaScript FFI to call onChange"

decorate :: JSVal -> Value -> IO ()
decorate = error "you need the JavaScript FFI to call decorate"

ascendTree :: JSVal -> IO JSVal
ascendTree = error "you need the JavaScript FFI to call ascendTree"

#endif
