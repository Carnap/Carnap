{-#LANGUAGE FlexibleContexts, RankNTypes #-}
module Carnap.GHCJS.Action.QualitativeProblem (qualitativeProblemAction) where

import Lib
import Carnap.GHCJS.SharedFunctions (simpleHash)
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.HTMLTextAreaElement (castToHTMLTextAreaElement, setValue, getValue, setSelectionEnd, getSelectionStart, setAutocapitalize, setAutocorrect)
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.Window (confirm)
import GHCJS.DOM.Node (appendChild, getParentNode)
import GHCJS.DOM.Document (createElement)
import GHCJS.DOM.EventM (newListener, addListener, EventM)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (newIORef, IORef, readIORef, writeIORef)
import Data.Map as M
import Data.Hashable
import Data.Maybe
import Data.Text (pack)
import Text.Read (readMaybe)

qualitativeProblemAction :: IO ()
qualitativeProblemAction = initElements getQualitativeProblems activateQualitativeProblem

getQualitativeProblems :: Document -> HTMLElement -> IO [Maybe (Element, Element, Map String String)]
getQualitativeProblems d = genInOutElts d "div" "div" "qualitative"

activateQualitativeProblem :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateQualitativeProblem w (Just (i,o,opts)) = do
        case M.lookup "qualitativetype" opts of
            Just "multiplechoice" -> createMultipleChoice w i o opts
            Just "shortanswer" -> createShortAnswer w i o opts
            _  -> return ()

submitQualitative :: Map String String -> IORef (Bool, String) -> String -> String -> EventM HTMLTextAreaElement e ()
submitQualitative opts ref g l = do (isDone,val) <- liftIO $ readIORef ref
                                    if isDone 
                                        then trySubmit Qualitative opts l (ProblemContent (pack g)) True
                                        else message "Not quite right. Try again?"

submitEssay :: Map String String -> Element -> String -> String -> EventM HTMLTextAreaElement e ()
submitEssay opts text g l = do manswer <- getValue . castToHTMLTextAreaElement $ text
                               case manswer of 
                                    Just answer -> trySubmit Qualitative opts l (QualitativeProblemDataOpts (pack g) (pack answer) (toList opts)) False
                                    Nothing -> message "It doesn't look like an answer has been written"

createMultipleChoice :: Document -> Element -> Element -> Map String String -> IO ()
createMultipleChoice w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        ref <- newIORef (False,"")
        setInnerHTML i (Just g)
        bw <- buttonWrapper w
        case M.lookup "submission" opts of
            Just s | take 7 s == "saveAs:" -> do
                let l = Prelude.drop 7 s
                bt1 <- doneButton w "Submit"
                appendChild bw (Just bt1)
                submit <- newListener $ submitQualitative opts ref g l
                addListener bt1 click submit False                
            _ -> return ()
        let choices = maybe [] lines $ M.lookup "content" opts
            labeledChoices = zip (Prelude.map getLabel choices) (Prelude.map isGood choices)
        radios <- mapM (toRadio g ref) labeledChoices
        mapM_ (appendChild o . Just . fst) radios
        Just par <- getParentNode o
        appendChild par (Just bw)
        return ()

    where getLabel s = case readMaybe s :: Maybe (Int, String) of
                         Just (_,s') -> s'
                         Nothing -> "indecipherable label"
          isGood s = case readMaybe s :: Maybe (Int, String) of
                        Just (h,s') -> h == simpleHash ('*':s')
                        Nothing -> False
          toRadio g ref (s,b) = do 
               Just input <- createElement w (Just "input")
               Just label <- createElement w (Just "label")
               Just wrapper <- createElement w (Just "div")
               mapM (uncurry $ setAttribute input) 
                     [ ("type","radio")
                     , ("name", g)
                     , ("id", g ++ "-" ++ s)
                     ]
               setInnerHTML label (Just s)
               update <- newListener $ liftIO (writeIORef ref (b,s))
               addListener input click update False
               setAttribute label "for" (g ++ "-" ++ s)
               appendChild wrapper (Just input)
               appendChild wrapper (Just label)
               return (wrapper, b)

createShortAnswer :: Document -> Element -> Element -> Map String String -> IO ()
createShortAnswer w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        setInnerHTML i (Just g)
        bw <- buttonWrapper w
        Just text <- createElement w (Just "textarea")
        case M.lookup "content" opts of
            Just t -> setValue (castToHTMLTextAreaElement text) (Just t)
            _ -> return ()
        appendChild o (Just text)
        case M.lookup "submission" opts of
            Just s | take 7 s == "saveAs:" -> do
                let l = Prelude.drop 7 s
                bt1 <- doneButton w "Submit"
                appendChild bw (Just bt1)
                submit <- newListener $ submitEssay opts text g l
                addListener bt1 click submit False                
            _ -> return ()
        Just par <- getParentNode o
        appendChild par (Just bw)
        return ()
