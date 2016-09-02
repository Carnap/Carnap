module Main where

import Carnap.Calculi.NaturalDeduction.Parser (toDisplaySequencePropProof)
import Lib
import GHCJS.DOM
import GHCJS.DOM.Element
--the import below is needed to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM.Types
import GHCJS.DOM.HTMLTextAreaElement (HTMLTextAreaElement, getValue)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Window (alert)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

main :: IO ()
main = runWebGUI $ \w -> 
        do (Just dom) <- webViewGetDomDocument w
           (Just b) <- getBody dom
           mcheckers <- getCheckers b
           case mcheckers of 
                [] -> return ()
                _ -> mapM_ (activateChecker dom) mcheckers

getCheckers :: IsElement self => self -> IO [Maybe (Element, Element, [String])]
getCheckers b = 
        do ldivs <- getListOfElementsByClass b "proofchecker"
           mapM extractCheckers ldivs
        where extractCheckers Nothing = return Nothing
              extractCheckers (Just div) = 
                do mi <- getFirstElementChild div
                   cn <- getClassName div
                   case mi of
                       Just i -> 
                         do mo <- getNextElementSibling i
                            case mo of (Just o) -> return $ Just (i,o,words cn)
                                       Nothing -> return Nothing
                       Nothing -> return Nothing

activateChecker :: Document -> Maybe (Element, Element,[String]) -> IO ()
activateChecker w (Just (i,o,classes)) = 
        do mfeedbackDiv@(Just fd) <- createElement w (Just "div")
           mnumberDiv@(Just nd) <-createElement w (Just "div")
           setAttribute fd "class" "proofFeedback"
           setAttribute nd "class" "numbering"
           appendChild o mnumberDiv
           appendChild o mfeedbackDiv
           echo <- newListener $ updateResults 
                        (listToUl w . toDisplaySequencePropProof) fd
           addListener i keyUp echo False
           setLinesTo w nd 5
           syncScroll i o
activateChecker _ Nothing  = return ()

updateResults :: (IsElement e, IsElement e') => 
    (String -> IO e') -> e -> EventM HTMLTextAreaElement KeyboardEvent ()
updateResults f o = 
        do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
           mv <- getValue t
           case mv of 
               Nothing -> return ()
               Just v -> do liftIO $ setInnerHTML o (Just "")
                            v' <- liftIO $ f v
                            appendChild o (Just v')
                            return ()

setLinesTo w nd n = do setInnerHTML nd (Just "")
                       linenos <- mapM toLineNo [1..n]
                       mapM (appendChild nd . Just) linenos
    where toLineNo m = do (Just lno) <- createElement w (Just "div")
                          setInnerHTML lno (Just $ show m ++ ".")
                          return lno

