module Carnap.GHCJS.Widget.ProofCheckBox (
    checkerWith, 
    CheckerOptions(..),
    CheckerFeedbackUpdate(..),
    Button(..)) where 
import Lib
import Data.IORef (IORef, newIORef,writeIORef,readIORef)
import GHCJS.DOM.Types
import GHCJS.DOM.Element (setAttribute, setInnerHTML,keyUp,click)
import GHCJS.DOM.Document (createElement, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode)
import GHCJS.DOM.EventM (EventM, target, newListener,addListener)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement,getValue)

data Button = Button { label  :: String 
                     , action :: IORef Bool -> Window -> Element -> 
                            EventM Element MouseEvent ()
                     }

data CheckerFeedbackUpdate = Keypress | Click String | Never

data CheckerOptions = CheckerOptions { submit :: Maybe Button -- What's the submission button, if there is one?
                                     , render :: Bool -- Should the checker render the proof?
                                     , directed :: Bool -- Is the checker directed towards a sequent?
                                     , feedback :: CheckerFeedbackUpdate --what type of feedback should the checker give?
                                     , initialUpdate :: Bool -- Should the checker be updated on load?
                                     }

checkerWith :: CheckerOptions -> (Document -> IORef Bool -> String -> (Element, Element) -> IO ()) -> IOGoal -> Document -> IO ()
checkerWith options updateres iog@(IOGoal i o g classes) w = do
           mfeedbackDiv@(Just fd) <- createElement w (Just "div")
           mnumberDiv@(Just nd) <- createElement w (Just "div")
           ref <- newIORef False
           setAttribute fd "class" "proofFeedback"
           setAttribute nd "class" "numbering"
           mpar@(Just par) <- getParentNode o               
           appendChild o mnumberDiv
           appendChild o mfeedbackDiv
           lineupd <- newListener $ onKey ["Enter","Backspace","Delete"] $ updateLines w nd
           (Just w') <- getDefaultView w
           addListener i keyUp lineupd False
           setLinesTo w nd 1
           syncScroll i o
           initlistener <- newListener $ genericUpdateResults2 (updateres w ref) g fd
           addListener i initialize initlistener False                
           case feedback options of
               Keypress -> do
                   kblistener <- newListener $ genericUpdateResults2 (updateres w ref) g fd
                   addListener i keyUp kblistener False
               Never -> return ()
               Click s -> do 
                   mbt@(Just bt) <- createElement w (Just "button")
                   setInnerHTML bt (Just s)         
                   appendChild par mbt
                   btlistener <- newListener $ genericUpdateResults2 (updateres w ref) g fd
                   addListener bt click btlistener False                
           case submit options of
               Just button -> do 
                   mbt'@(Just bt') <- createElement w (Just "button")
                   setInnerHTML bt' (Just (label button))         
                   appendChild par mbt'
                   buttonAct <- newListener $ (action button) ref w' i
                   addListener bt' click buttonAct False                
               Nothing -> return ()
           mv <- getValue (castToHTMLTextAreaElement i)
           case mv of
               Nothing -> return ()
               (Just iv) -> do setLinesTo w nd (1 + length (lines iv))
                               if initialUpdate options then updateres w ref iv (g, fd) else return ()

updateLines :: (IsElement e) => Document -> e -> EventM HTMLTextAreaElement KeyboardEvent ()
updateLines w nd =  do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
                       mv <- getValue t
                       case mv of 
                           Nothing -> return ()
                           Just v -> setLinesTo w nd (1 + length (lines v))
                                      
setLinesTo w nd n = do setInnerHTML nd (Just "")
                       linenos <- mapM toLineNo [1 .. n]
                       mapM_ (appendChild nd . Just) linenos
    where toLineNo m = do (Just lno) <- createElement w (Just "div")
                          setInnerHTML lno (Just $ show m ++ ".")
                          return lno
