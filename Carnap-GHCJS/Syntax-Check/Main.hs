module Main where

import Lib
import GHCJS.DOM
import GHCJS.DOM.Element as E
import GHCJS.DOM.HTMLInputElement
import GHCJS.DOM.Document
import GHCJS.DOM.Node
import GHCJS.DOM.Event
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import GHCJS.DOM.EventTarget
import Control.Monad.IO.Class (liftIO)

main :: IO ()
main = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               (Just i) <- createElement dom (Just "input")
               (Just o) <- createElement dom (Just "span")
               (Just b) <- getBody dom
               echo     <- newListener $ echoTo setInnerHTML o
               addListener i E.keyUp echo False
               appendChild b (Just i)
               appendChild b (Just o)
               return ()

echoTo :: (element -> Maybe String -> IO ()) -> element -> EventM HTMLInputElement KeyboardEvent ()
echoTo f o = do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                mv <- getValue t
                case mv of 
                    Nothing -> return ()
                    Just v -> liftIO $ f o mv
