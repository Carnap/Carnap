module Main where

import Lib
import Carnap.Languages.PurePropositional.Parser
import Text.Parsec
import GHCJS.DOM
import GHCJS.DOM.Element
--the import below is here to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM.Types
import GHCJS.DOM.HTMLInputElement
import GHCJS.DOM.Document (createElement, getBody)
import GHCJS.DOM.Node
import GHCJS.DOM.NodeList
import GHCJS.DOM.Event
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import GHCJS.DOM.EventTarget
import Control.Monad.IO.Class (liftIO)

main :: IO ()
main = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               (Just b) <- getBody dom
               mcheckers <- getCheckers b
               mapM activateChecker mcheckers
               return ()

echoTo :: IsElement element => (String -> String) -> element -> EventM HTMLInputElement KeyboardEvent ()
echoTo f o = do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                mv <- getValue t
                case mv of 
                    Nothing -> return ()
                    Just v -> liftIO $ setInnerHTML o (fmap f mv)

tryParse s = unPack $ parse purePropFormulaParser "" s 
    where unPack (Right s) = show s
          unPack (Left e)  = show e

listOfNodesByClass :: IsElement self => self -> String -> IO [Maybe Node]
listOfNodesByClass elt c = do mnl <- getElementsByClassName elt c
                              case mnl of 
                                Nothing -> return []
                                Just nl -> do l <- getLength nl
                                              mapM (item nl) [0 .. l-1]

getCheckers :: IsElement self => self -> IO [Maybe (Element, Element)]
getCheckers b = do lspans <- listOfNodesByClass b "synchecker"
                   mapM extractCheckers lspans
        where extractCheckers Nothing = return Nothing
              extractCheckers (Just span) = do mi <- getFirstElementChild (castToElement span)
                                               case mi of
                                                   Just i -> do mo <- getNextElementSibling i
                                                                case mo of (Just o) -> return $ Just (i,o)
                                                                           Nothing -> return Nothing
                                                   Nothing -> return Nothing
                

activateChecker :: (IsElement element, IsElement t) => Maybe (t, element) -> IO ()
activateChecker Nothing    = return ()
activateChecker (Just (i,o)) = do echo <- newListener $ echoTo tryParse o
                                  addListener i keyUp echo False
