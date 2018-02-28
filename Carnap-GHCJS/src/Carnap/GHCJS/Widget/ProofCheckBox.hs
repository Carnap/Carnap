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
import Control.Monad (when)
import Control.Concurrent
import GHCJS.DOM.Types
import GHCJS.DOM.Element (setAttribute, setInnerHTML,keyDown,keyUp,click,getScrollWidth,getScrollHeight)
import GHCJS.DOM.Document (createElement, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode)
import GHCJS.DOM.EventM (EventM, target, newListener,addListener)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement,setValue,getValue,setSelectionEnd,getSelectionStart)

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
                                     , autoIndent :: Bool -- Should the checker indent automatically?
                                     , autoResize :: Bool -- Should the checker resize automatically?
                                     }

checkerWith :: CheckerOptions -> (Document -> IORef Bool -> String -> (Element, Element) -> IO ()) -> IOGoal -> Document -> IO ()
checkerWith options updateres iog@(IOGoal i o g content _) w = do
           [Just fd, Just nd, Just sd, Just incompleteAlert] <- mapM (createElement w . Just) ["div","div","div","div"]
           ref <- newIORef False
           setInnerHTML i (Just content)
           setAttribute fd "class" "proofFeedback"
           setAttribute nd "class" "numbering"
           setAttribute sd "class" "proofSpinner"
           setAttribute incompleteAlert "class" "incompleteAlert"
           popUpWith g w incompleteAlert "⚠" 
                ("This proof does not establish that this conclusion follows from these premises."
                ++ "Make sure that you've only used legitimate premises, and have discharged all assumptions!")
                Nothing
           setInnerHTML sd (Just spinnerHtml)
           mpar@(Just par) <- getParentNode o               
           mapM_ (appendChild o . Just) [nd, fd]
           mapM_ (appendChild g . Just) [sd, incompleteAlert]
           (Just w') <- getDefaultView w
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
           when (autoIndent options) $ do
                   indentlistener <- newListener (onEnter reindent)
                   addListener i keyUp indentlistener False
           when (autoResize options) $ do
                   resizelistener <- newListener (do Just t <- target; resize t)
                   resizelistener' <- newListener (do Just t <- target; resize t)
                   addListener i keyDown resizelistener False
                   addListener i initialize resizelistener'  False
                   resize i
           case submit options of
               Just button -> do 
                   mbt'@(Just bt') <- createElement w (Just "button")
                   setInnerHTML bt' (Just (label button))         
                   appendChild par mbt'
                   buttonAct <- newListener $ action button ref w' i
                   addListener bt' click buttonAct False                
               Nothing -> return ()
           lineupd <- newListener $ updateLines w nd (indentGuides options)
           addListener i keyUp lineupd False
           mv <- getValue (castToHTMLTextAreaElement i)
           case mv of
               Nothing -> setLinesTo w nd (indentGuides options) [" "]
               (Just iv) -> do setLinesTo w nd (indentGuides options) (altlines iv)
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
                                     Just v -> liftIO $ setLinesTo w nd hasguides (altlines v)

reindent :: EventM HTMLTextAreaElement KeyboardEvent ()
reindent = do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
              mv <- getValue t
              case mv of 
                  Nothing -> return ()
                  Just v -> do
                      pos <- getSelectionStart t
                      let (pre,post) = splitAt pos v
                          line = last . lines $ pre
                          ws = takeWhile (`elem` [' ','\t']) line
                      setValue t $ Just ( pre ++ ws ++ post )
                      setSelectionEnd t (length (pre ++ ws))

resize :: MonadIO m => Element -> m ()
resize i = do setAttribute i "style" "width: 0px;height: 0px"
              mpar@(Just par) <- getParentNode i
              w <- getScrollWidth i
              h <- getScrollHeight i
              setAttribute i "style" "resize:none;"
              setAttribute (castToHTMLElement par) 
                    "style" ("width:" ++ (show $ max 400 (w + 50)) ++ "px;" ++ 
                    "height:" ++ (show $ max 120 (h + 20)) ++ "px;")

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

--a version of `lines` that pays attention to a trailing newline.
altlines s = case break (=='\n') s of (l, s') -> l : rec s' 
        where rec s' = case s' of 
                          [] -> []
                          _:s'' -> altlines s''
