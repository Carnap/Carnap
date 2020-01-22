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

getQualitativeProblems :: Document -> HTMLElement -> IO [Maybe (Element, Element, M.Map String String)]
getQualitativeProblems d = genInOutElts d "div" "div" "qualitative"

activateQualitativeProblem :: Document -> Maybe (Element, Element, M.Map String String) -> IO ()
activateQualitativeProblem w (Just (i,o,opts)) = do
        case M.lookup "qualitativetype" opts of
            Just "multiplechoice" -> createMultipleChoice w i o opts
            Just "shortanswer" -> createShortAnswer w i o opts
            _  -> return ()

submitQualitative :: IsEvent e => M.Map String String -> IORef (Bool, String) -> String -> String -> EventM Element e ()
submitQualitative opts ref g l = do (isDone,val) <- liftIO $ readIORef ref
                                    let submission = (QualitativeProblemDataOpts (pack g) (pack val) (toList opts))
                                    if isDone || ("exam" `inOpts` opts)
                                        then trySubmit Qualitative opts l submission isDone
                                        else message "Not quite right. Try again?"

submitEssay :: IsEvent e => M.Map String String -> Element -> String -> String -> EventM HTMLTextAreaElement e ()
submitEssay opts text g l = do manswer <- getValue . castToHTMLTextAreaElement $ text
                               case manswer of 
                                    Just answer -> trySubmit Qualitative opts l (QualitativeProblemDataOpts (pack g) (pack answer) (toList opts)) False
                                    Nothing -> message "It doesn't look like an answer has been written"

createMultipleChoice :: Document -> Element -> Element -> M.Map String String -> IO ()
createMultipleChoice w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        ref <- newIORef (False,"")
        setInnerHTML i (Just g)
        bw <- createButtonWrapper w o
        let submit = submitQualitative opts ref g
        btStatus <- createSubmitButton w bw submit opts
        if "check" `inOpts` opts then do
              bt2 <- questionButton w "Check"
              appendChild bw (Just bt2)
              checkIt <- newListener $ do 
                              (isDone,_) <- liftIO $ readIORef ref
                              if isDone 
                                  then message "Correct!" 
                                  else message "Not quite right. Try again?"
              addListener bt2 click checkIt False                
        else return ()
        let choices = maybe [] lines $ M.lookup "content" opts
            labeledChoices = zip3 (Prelude.map getLabel choices) 
                                  (Prelude.map isGood choices) 
                                  (Prelude.map isChecked choices)
        radios <- mapM (toRadio g ref) labeledChoices
        mapM_ (appendChild o . Just . fst) radios
        doOnce o change False $ liftIO $ btStatus Edited
        return ()
        
    where
          getLabel s = if "nocipher" `inOpts` opts
                           then dropWhile (`elem` "+-*") s
                           else case readMaybe s :: Maybe (Int, String) of
                                 Just (_,s') -> s'
                                 Nothing -> "indecipherable label"
          isGood s = if "nocipher" `inOpts` opts
                         then case s of ('*':_) -> True; ('+':_) -> True; _ -> False
                         else case readMaybe s :: Maybe (Int, String) of
                                Just (h,s') -> h `elem` [simpleHash ('*':s'), simpleHash ('+':s')]
                                Nothing -> False
          isChecked s = if "nocipher" `inOpts` opts
                         then case s of ('-':_) -> True; ('+':_) -> True; _ -> False
                         else case readMaybe s :: Maybe (Int, String) of
                                Just (h,s') -> h `elem` [simpleHash ('-':s'), simpleHash ('+':s')]
                                Nothing -> False
          toRadio g ref (s,b,c) = do 
               Just input <- createElement w (Just "input")
               Just label <- createElement w (Just "label")
               Just wrapper <- createElement w (Just "div")
               if c then writeIORef ref (b,s) else return ()
               mapM (uncurry $ setAttribute input) $
                     [ ("type","radio")
                     , ("name", g)
                     , ("id", g ++ "-" ++ s)
                     ] ++ if c then [("checked","checked")] else []
               setInnerHTML label (Just s)
               update <- newListener $ liftIO (writeIORef ref (b,s))
               addListener input click update False
               setAttribute label "for" (g ++ "-" ++ s)
               appendChild wrapper (Just input)
               appendChild wrapper (Just label)
               return (wrapper, b)

createShortAnswer :: Document -> Element -> Element -> M.Map String String -> IO ()
createShortAnswer w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        setInnerHTML i (Just g)
        bw <- createButtonWrapper w o
        Just text <- createElement w (Just "textarea")
        case M.lookup "content" opts of
            Just t -> setValue (castToHTMLTextAreaElement text) (Just t)
            _ -> return ()
        appendChild o (Just text)
        case M.lookup "submission" opts of
            Just s | Prelude.take 7 s == "saveAs:" -> do
                let l = Prelude.drop 7 s
                bt1 <- doneButton w "Submit"
                appendChild bw (Just bt1)
                submit <- newListener $ submitEssay opts text g l
                addListener bt1 click submit False                
            _ -> return ()
        return ()
