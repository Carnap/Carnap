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

getCheckers :: IsElement self => self -> IO [Maybe (Element, Element, Element, [String])]
getCheckers b = 
        do ldivs <- getListOfElementsByClass b "proofchecker"
           mapM extractCheckers ldivs
        where extractCheckers Nothing = return Nothing
              extractCheckers (Just div) = 
                do mg <- getFirstElementChild div
                   cn <- getClassName div
                   case mg of
                       Nothing -> return Nothing
                       Just g -> 
                         do mi <- getNextElementSibling g
                            case mi of 
                               Nothing -> return Nothing
                               (Just i) -> 
                                    do mo <- getNextElementSibling i
                                       case mo of 
                                           Nothing -> return Nothing
                                           (Just o) -> return $ Just (i,o,g,words cn)

activateChecker :: Document -> Maybe (Element, Element, Element, [String]) -> IO ()
activateChecker w (Just (i,o,g, classes)) = 
        do mfeedbackDiv@(Just fd) <- createElement w (Just "div")
           mnumberDiv@(Just nd) <-createElement w (Just "div")
           setAttribute fd "class" "proofFeedback"
           setAttribute nd "class" "numbering"
           appendChild o mnumberDiv
           appendChild o mfeedbackDiv
           echo <- newListener $ updateResults 
                        (genericListToUl wrap w . snd . toDisplaySequencePropProof) fd
           lineupd <- newListener $ onEnter $ updateLines w nd
           addListener i keyUp echo False
           addListener i keyUp lineupd False
           setLinesTo w nd 1
           syncScroll i o
    where wrap (Left "") ="<div>&nbsp;</div>"
          wrap (Left s) = "<div>✗<span>" ++ s ++ "</span></div>"
          wrap (Right seq) = "<div>+<span>" ++ show seq ++ "</span></div>"
activateChecker _ Nothing  = return ()

-- XXX: this should be a library function
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

updateResults2 :: (IsElement e, IsElement e', IsElement e'', IsElement e''') => 
    (String -> IO (e'', e''')) -> e -> e' -> EventM HTMLTextAreaElement KeyboardEvent ()
updateResults2 f o o' = 
        do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
           mv <- getValue t
           case mv of 
               Nothing -> return ()
               Just v -> do liftIO $ setInnerHTML o (Just "")
                            liftIO $ setInnerHTML o' (Just "")
                            (v',v'') <- liftIO $ f v
                            appendChild o (Just v')
                            appendChild o' (Just v'')
                            return ()

updateLines :: (IsElement e) => Document -> e -> EventM HTMLTextAreaElement KeyboardEvent ()
updateLines w nd = onEnter $ do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
                                mv <- getValue t
                                case mv of 
                                    Nothing -> return ()
                                    Just v -> setLinesTo w nd (1 + (length $ lines v))
                                      
setLinesTo w nd n = do setInnerHTML nd (Just "")
                       linenos <- mapM toLineNo [1 .. n]
                       mapM_ (appendChild nd . Just) linenos
    where toLineNo m = do (Just lno) <- createElement w (Just "div")
                          setInnerHTML lno (Just $ show m ++ ".")
                          return lno

