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
import Control.Monad.Trans.State.Lazy
import Control.Monad.IO.Class
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
                                     , indentGuides :: Bool -- Should the checker display indentation guides?
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
           lineupd <- newListener $ updateLines w nd (indentGuides options) --formerly onKey ["Enter","Backspace","Delete"] $
           (Just w') <- getDefaultView w
           addListener i keyUp lineupd False
           syncScroll i o
           --respond to custom initialize events
           initlistener <- newListener $ updateWithValue (\s -> updateres w ref s (g,fd))
           addListener i initialize initlistener False                
           case feedback options of
               Keypress -> do
                   kblistener <- newListener $ updateWithValue (\s -> updateres w ref s (g,fd))
                   addListener i keyUp kblistener False
               Never -> return ()
               Click -> do 
                   mbt@(Just bt) <- createElement w (Just "button")
                   setInnerHTML bt (Just "Check Proof")         
                   appendChild par mbt
                   btlistener <- newListener $ updateWithValue (\s -> updateres w ref s (g,fd))
                   addListener bt click btlistener False                
           case submit options of
               Just button -> do 
                   mbt'@(Just bt') <- createElement w (Just "button")
                   setInnerHTML bt' (Just (label button))         
                   appendChild par mbt'
                   buttonAct <- newListener $ action button ref w' i
                   addListener bt' click buttonAct False                
               Nothing -> return ()
           mv <- getValue (castToHTMLTextAreaElement i)
           case mv of
               Nothing -> setLinesTo w nd (indentGuides options) [" "]
               (Just iv) -> do setLinesTo w nd (indentGuides options) (lines iv)
                               if initialUpdate options then updateres w ref iv (g, fd) else return ()

spinnerHtml = renderHtml [shamlet|
<svg version="1.1" id="loader-1" xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" x="0px" y="0px" width="30px" height="30px" viewBox="0 0 40 40" enable-background="new 0 0 40 40" xml:space="preserve">
    <path opacity="0.2" fill="#000" d="M20.201,5.169c-8.254,0-14.946,6.692-14.946,14.946c0,8.255,6.692,14.946,14.946,14.946 s14.946-6.691,14.946-14.946C35.146,11.861,28.455,5.169,20.201,5.169z M20.201,31.749c-6.425,0-11.634-5.208-11.634-11.634 c0-6.425,5.209-11.634,11.634-11.634c6.425,0,11.633,5.209,11.633,11.634C31.834,26.541,26.626,31.749,20.201,31.749z"/>
    <path fill="#000" d="M26.013,10.047l1.654-2.866c-2.198-1.272-4.743-2.012-7.466-2.012h0v3.312h0 C22.32,8.481,24.301,9.057,26.013,10.047z">
        <animateTransform attributeType="xml" attributeName="transform" type="rotate" from="0 20 20" to="360 20 20" dur="0.5s" repeatCount="indefinite"/>|]

updateLines :: (IsElement e) => Document -> e -> Bool -> EventM HTMLTextAreaElement KeyboardEvent ()
updateLines w nd hasguides =  do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
                                 mv <- getValue t
                                 case mv of 
                                     Nothing -> return ()
                                     Just v -> liftIO $ setLinesTo w nd hasguides (lines v)
                                      
setLinesTo :: (IsElement e) => Document -> e -> Bool -> [String] -> IO ()
setLinesTo w nd hasguides [] = setLinesTo w nd hasguides [""]
setLinesTo w nd hasguides lines = do setInnerHTML nd (Just "")
                                     overlays <- evalStateT (mapM toLineNo lines) (0,[])
                                     mapM_ (appendChild nd . Just) overlays
    where toLineNo :: String -> StateT (Int,[Int]) IO Element
          toLineNo l = do (no,guidelevels) <- get --line number and guide levels of previous line
                          (Just overlay) <- liftIO $ createElement w (Just "div")
                          let (indent,rest) = (takeWhile (== ' ') l, dropWhile (== ' ') l)
                          let guidelevels'= dropWhile (\x -> (length indent) <= x) guidelevels --remove guides below current indentation
                          let guidestring = if hasguides 
                                            then reverse . concat . map (\n -> '│' : replicate (n - 1) ' ') $ differences guidelevels'
                                            else ""
                          let prespace  | no < 9  = "   "
                                        | no < 99  = "  "
                                        | no < 999  = " "
                                        | otherwise  = ""
                          liftIO $ setInnerHTML overlay (Just $ prespace ++ show (no + 1) ++ ". " ++ guidestring)
                          let guidelevels'' = if take 4 rest `elem` ["show","Show","SHOW"] 
                                              then length indent : guidelevels' 
                                              else guidelevels' 
                          put (no + 1, guidelevels'')
                          return overlay

          differences (x:y:l) = x - y : differences (y:l)
          differences [x]     = [x]
          differences []      = []
