{-# LANGUAGE QuasiQuotes #-}
module Carnap.GHCJS.Widget.ProofCheckBox (
    checkerWith, 
    CheckerOptions(..),
    CheckerFeedbackUpdate(..),
    optionsFromMap,
    Button(..)) where 
import Lib
import Data.Maybe (catMaybes)
import qualified Data.Map as M (lookup) 
import Data.IORef (IORef, newIORef,writeIORef,readIORef)
import Control.Monad.Trans.State.Lazy
import Control.Monad.IO.Class
import Control.Monad (when)
import Control.Concurrent
import GHCJS.DOM.Types
import GHCJS.DOM.Element (setAttribute, getAttribute, getInnerHTML, setInnerHTML, keyDown, keyUp, click, getScrollWidth, getScrollHeight)
import GHCJS.DOM.HTMLElement (castToHTMLElement, setSpellcheck)
import GHCJS.DOM.Document (createElement, getDefaultView, getBody, getHead, getDomain, setDomain,getElementsByTagName)
import GHCJS.DOM.Window (open,getDocument)
import GHCJS.DOM.Node (appendChild, removeChild, getParentNode, cloneNode)
import GHCJS.DOM.EventM (EventM, target, newListener,addListener)
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, setValue, getValue, setSelectionEnd, getSelectionStart, setAutocapitalize, setAutocorrect)

data Button = Button { label  :: String 
                     , action :: IORef Bool -> Window -> Element -> 
                            EventM Element MouseEvent ()
                     }

data CheckerFeedbackUpdate = Keypress | Click | Never | SyntaxOnly
    deriving Eq

data CheckerGuide = MontagueGuide | FitchGuide | HausmanGuide | HowardSnyderGuide | NoGuide

data CheckerOptions = CheckerOptions { submit :: Maybe Button -- What's the submission button, if there is one?
                                     , render :: Bool -- Should the checker render the proof?
                                     , directed :: Bool -- Is the checker directed towards a sequent?
                                     , feedback :: CheckerFeedbackUpdate --what type of feedback should the checker give?
                                     , alternateSymbols :: String -> String
                                     , initialUpdate :: Bool -- Should the checker be updated on load?
                                     , indentGuides :: CheckerGuide -- How should the checker display indentation guides?
                                     , autoIndent :: Bool -- Should the checker indent automatically?
                                     , autoResize :: Bool -- Should the checker resize automatically?
                                     , popout :: Bool -- Should the checker be able to be put in a new window?
                                     , hideNumbering :: Bool -- Should the checker hide the line numbering
                                     }

optionsFromMap opts = CheckerOptions { submit = Nothing
                                      , feedback = case M.lookup "feedback" opts of
                                                       Just "manual" -> Click
                                                       Just "none" -> Never
                                                       Just "syntaxonly" -> SyntaxOnly
                                                       _ -> Keypress
                                      , directed = case M.lookup "goal" opts of
                                                       Just _ -> True
                                                       Nothing -> False
                                      , initialUpdate = case M.lookup "init" opts of
                                                       Just _ -> True
                                                       Nothing -> False
                                      , alternateSymbols = case M.lookup "alternate-symbols" opts of
                                                               Just "alt1" -> alternateSymbols1
                                                               Just "alt2" -> alternateSymbols2
                                                               Just "alt3" -> alternateSymbols3
                                                               _ -> id
                                      , indentGuides = case M.lookup "guides" opts of
                                                       Just "montague"     -> MontagueGuide
                                                       Just "fitch"        -> FitchGuide
                                                       Just "hausman"      -> HausmanGuide
                                                       Just "howardSnyder" -> HowardSnyderGuide
                                                       _ -> if "guides" `elem` optlist 
                                                                then MontagueGuide
                                                                else NoGuide
                                      , render = "render" `elem` optlist
                                      , autoIndent = "indent" `elem` optlist
                                      , autoResize= "resize" `elem` optlist
                                      , popout = "popout" `elem` optlist
                                      , hideNumbering = "hideNumbering" `elem` optlist
                                      }
                where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

checkerWith :: CheckerOptions -> (Document -> IORef Bool -> String -> (Element, Element) -> IO ()) -> IOGoal -> Document -> IO ()
checkerWith options updateres iog@(IOGoal i o g content _) w = do
           ref <- newIORef False
           elts <- mapM (createElement w . Just) ["div","div","div","div","div"]
           let [Just fd, Just nd, Just sd, Just incompleteAlert, Just aligner] = elts
           bw <- buttonWrapper w
           setSpellcheck (castToHTMLElement i) False
           setAutocapitalize (castToHTMLTextAreaElement i) (Just "off")
           setAutocorrect (castToHTMLTextAreaElement i) False
           setAttribute i "data-gramm" "false" -- attempt to disable grammarly
           setInnerHTML i (Just content)
           setAttribute aligner "class" "aligner"
           setAttribute fd "class" "proofFeedback"
           setAttribute nd "class" "numbering"
           setAttribute sd "class" "proofSpinner"
           setAttribute incompleteAlert "class" "incompleteAlert"
           popUpWith g w incompleteAlert "⚠" 
                ("This proof does not establish that this conclusion follows from these premises. "
                ++ "Perhaps there's an unwarranted assumption being used?")
                Nothing
           setInnerHTML sd (Just spinnerSVG)
           mpar@(Just par) <- getParentNode o
           mapM_ (appendChild o . Just) (if hideNumbering options then [fd] else [nd, fd])
           mapM_ (appendChild aligner . Just) [o, i]
           mapM_ (appendChild g . Just) [sd, incompleteAlert]
           mapM_ (appendChild par . Just) [aligner,bw]
           (Just w') <- getDefaultView w
           syncScroll i o
           --respond to custom initialize events
           initlistener <- newListener $ updateWithValue (\s -> updateres w ref s (g,fd))
           addListener i initialize initlistener False                
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
                   bt' <- doneButton w (label button)
                   appendChild bw  (Just bt')
                   buttonAct <- newListener $ action button ref w' i
                   addListener bt' click buttonAct False                
               Nothing -> return ()
           case feedback options of
               Never -> return ()
               Click -> do 
                   bt <- questionButton w "Check"
                   appendChild bw (Just bt)
                   btlistener <- newListener $ liftIO $
                                    do miv <-  getValue (castToHTMLTextAreaElement i)
                                       case miv of Just iv -> updateres w ref iv (g, fd)
                                                   Nothing -> return ()
                   addListener bt click btlistener True
               _ -> do
                   kblistener <- newListener $ updateWithValue (\s -> updateres w ref s (g,fd))
                   addListener i keyUp kblistener False
           when (popout options) $ do
               btpop <- expandButton w "Expand"
               appendChild bw (Just btpop)
               thepopout <- newListener $ liftIO $ popoutWith options updateres iog w
               addListener btpop click thepopout False
           lineupd <- newListener $ updateLines w nd options
           clearThePoppers <- newListener $ clearPoppers aligner
           addListener i keyUp lineupd False
           addListener i keyUp clearThePoppers False
           mv <- getValue (castToHTMLTextAreaElement i)
           case mv of
               Nothing -> setLinesTo w nd options [" "]
               (Just iv) -> do setLinesTo w nd options (altlines iv)
                               if initialUpdate options then updateres w ref iv (g, fd) else return ()

popoutWith :: CheckerOptions -> (Document -> IORef Bool -> String -> (Element, Element) -> IO ()) -> IOGoal -> Document -> IO ()
popoutWith options updateres iog@(IOGoal i o g content opts) dom = do
            (Just win) <- getDefaultView dom
            (Just popwin) <- open win "" "" ""
            (Just popdom) <- getDocument popwin 
            (Just body) <- getBody popdom
            (Just head) <- getHead popdom
            (getDomain dom :: IO (Maybe String)) >>= setDomain popdom
            links <- getElementsByTagName dom "link" >>= maybeNodeListToList
            newlinks <- map castToElement . catMaybes <$> mapM (\x -> cloneNode x False) (catMaybes links)
            mapM_ (appendChild head . Just) newlinks
            [g', o', i'] <- map castToElement . catMaybes <$> mapM (\x -> cloneNode x False) [g,o,i]
            let newOptions = options { autoResize = False
                                     , initialUpdate = True
                                     , popout = False
                                     } 
            (getInnerHTML g :: IO (Maybe String)) >>= setInnerHTML g'
            (Just par) <- getParentNode i
            (Just gpar) <- getParentNode par
            (Just optstring) <- getAttribute (castToElement gpar) "data-carnap-options" :: IO (Maybe String)
            setAttribute body "data-carnap-options" optstring
            setAttribute body "data-carnap-type" "proofchecker"
            mapM (appendChild body . Just) [g', i', o']
            checkerWith newOptions updateres (IOGoal i' o' g' content opts) popdom

updateLines :: (IsElement e) => Document -> e -> CheckerOptions -> EventM HTMLTextAreaElement KeyboardEvent ()
updateLines w nd options =  do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
                               mv <- getValue t
                               case mv of 
                                     Nothing -> return ()
                                     Just v -> liftIO $ setLinesTo w nd options (altlines v)

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
              (Just par) <- getParentNode i
              (Just gpar) <- getParentNode par
              w <- getScrollWidth i
              h <- getScrollHeight i
              setAttribute i "style" "resize:none;"
              setAttribute (castToHTMLElement gpar) 
                    "style" ("width:" ++ (show $ max 400 (w + 50)) ++ "px;" ++ 
                    "height:" ++ (show $ max 120 (h + 20)) ++ "px;")

clearPoppers :: (IsElement e, MonadIO m) => e -> m ()
clearPoppers target = do mpoppers <- liftIO $ getListOfElementsByClass target "popperWrapper"
                         mapM_ (liftIO . removeChild target) mpoppers

setLinesTo :: (IsElement e) => Document -> e -> CheckerOptions -> [String] -> IO ()
setLinesTo w nd options [] = setLinesTo w nd options [""]
setLinesTo w nd options lines = do setInnerHTML nd (Just "")
                                   let indents = map (length . takeWhile ((==) ' ')) lines
                                   overlays <- evalStateT (mapM (toLineNo indents) lines) (0,[])
                                   mapM_ (appendChild nd . Just) overlays
    where toLineNo :: [Int] -> String -> StateT (Int,[Int]) IO Element
          toLineNo indents l =
              do (no,guidelevels) <- get --line number, guide levels of previous line
                 (Just overlay) <- liftIO $ createElement w (Just "div")
                 let rest = dropWhile (== ' ') l
                 let indent = indents !! no
                     oldindent = if no > 0 then indents !! (no - 1) else 0
                     nextindent = if no + 1 < length indents then indents !! (no + 1) else 0
                 let guidelevels' = dropWhile (\x -> indent <= x) guidelevels --remove guides below current indentation
                 let guidelevels'' = case indentGuides options of
                                         NoGuide -> []
                                         MontagueGuide | take 4 rest `elem` ["show","Show","SHOW"] -> indent : guidelevels'
                                         _ | indent > oldindent -> indent - 1 : guidelevels'
                                         _ -> guidelevels'
                 let guidestring = case indentGuides options of
                                       --TODO: clean this up
                                       NoGuide -> ""
                                       MontagueGuide -> reverse . concat . map (\n -> '│' : replicate (n - 1) ' ') $ differences guidelevels'
                                       HausmanGuide | indent > oldindent -> 
                                           reverse . concat 
                                           $ (\n -> '↱' : replicate (n - 1) ' ') (head $ differences guidelevels'')
                                             : map (\n -> '│' : replicate (n - 1) ' ') (tail $ differences guidelevels'')
                                       HausmanGuide | nextindent < indent && not (null guidelevels'') -> 
                                           (reverse . concat $ map (\n -> '│' : replicate (n - 1) ' ') (differences guidelevels''))
                                           ++ replicate (length rest + indent - (head guidelevels'')) '_'
                                       HowardSnyderGuide | indent > oldindent -> 
                                           reverse . concat 
                                           $ (\n -> "‾│" ++ replicate (n - 1) ' ') (head $ differences guidelevels'')
                                             : map (\n -> '│' : replicate (n - 1) ' ') (tail $ differences guidelevels'')
                                       HowardSnyderGuide | nextindent < indent && not (null guidelevels'') -> 
                                           (reverse . concat $ map (\n -> '│' : replicate (n - 1) ' ') (differences guidelevels''))
                                           ++ "_"
                                       FitchGuide | indent > oldindent -> 
                                           (reverse . concat $ map (\n -> '│' : replicate (n - 1) ' ') (differences guidelevels''))
                                           ++ replicate (length rest + indent - (head guidelevels'')) '_'
                                       _ -> reverse . concat . map (\n -> '│' : replicate (n - 1) ' ') $ differences guidelevels''
                 let prespace  | no < 9  = "   "
                               | no < 99  = "  "
                               | no < 999  = " "
                               | otherwise  = ""
                 liftIO $ setInnerHTML overlay (Just $ prespace ++ show (no + 1) ++ "." ++ guidestring)
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
