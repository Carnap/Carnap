{-# LANGUAGE QuasiQuotes #-}
module Carnap.GHCJS.Widget.ProofCheckBox (
    checkerWith, 
    CheckerOptions(..),
    CheckerFeedbackUpdate(..),
    Button(..)) where 
import Lib
import Data.IORef (IORef, newIORef,writeIORef,readIORef)
import Text.Hamlet
import Text.Blaze.Html.Renderer.String
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

data CheckerFeedbackUpdate = Keypress | Click | Never

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
           mspinnerDiv@(Just sd) <- createElement w (Just "div")
           ref <- newIORef False
           setAttribute fd "class" "proofFeedback"
           setAttribute nd "class" "numbering"
           setAttribute sd "class" "proofSpinner"
           setInnerHTML sd (Just spinnerHtml)
           mpar@(Just par) <- getParentNode o               
           appendChild o mnumberDiv
           appendChild o mfeedbackDiv
           appendChild g mspinnerDiv
           lineupd <- newListener $ onKey ["Enter","Backspace","Delete"] $ updateLines w nd
           (Just w') <- getDefaultView w
           addListener i keyUp lineupd False
           setLinesTo w nd 1
           syncScroll i o
           --respond to custom initialize events
           initlistener <- newListener $ genericUpdateResults2 (updateres w ref) g fd
           addListener i initialize initlistener False                
           case feedback options of
               Keypress -> do
                   kblistener <- newListener $ genericUpdateResults2 (updateres w ref) g fd
                   addListener i keyUp kblistener False
               Never -> return ()
               Click -> do 
                   mbt@(Just bt) <- createElement w (Just "button")
                   setInnerHTML bt (Just "Check Proof")         
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

spinnerHtml = renderHtml [shamlet|
<svg version="1.1" id="loader-1" xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" x="0px" y="0px" width="30px" height="30px" viewBox="0 0 40 40" enable-background="new 0 0 40 40" xml:space="preserve">
    <path opacity="0.2" fill="#000" d="M20.201,5.169c-8.254,0-14.946,6.692-14.946,14.946c0,8.255,6.692,14.946,14.946,14.946 s14.946-6.691,14.946-14.946C35.146,11.861,28.455,5.169,20.201,5.169z M20.201,31.749c-6.425,0-11.634-5.208-11.634-11.634 c0-6.425,5.209-11.634,11.634-11.634c6.425,0,11.633,5.209,11.633,11.634C31.834,26.541,26.626,31.749,20.201,31.749z"/>
    <path fill="#000" d="M26.013,10.047l1.654-2.866c-2.198-1.272-4.743-2.012-7.466-2.012h0v3.312h0 C22.32,8.481,24.301,9.057,26.013,10.047z">
        <animateTransform attributeType="xml" attributeName="transform" type="rotate" from="0 20 20" to="360 20 20" dur="0.5s" repeatCount="indefinite"/>|]

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
