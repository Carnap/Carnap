{-#LANGUAGE FlexibleContexts, RankNTypes #-}
module Carnap.GHCJS.Action.QualitativeProblem (qualitativeProblemAction) where

import Lib
import Carnap.GHCJS.SharedFunctions (simpleHash, simpleDecipher)
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.HTMLTextAreaElement as T (castToHTMLTextAreaElement, setValue, getValue, setSelectionEnd, getSelectionStart, setAutocapitalize, setAutocorrect) 
import GHCJS.DOM.HTMLInputElement as I (getValue) 
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
            Just "numerical" -> createNumerical w i o opts
            _  -> return ()

submitQualitative :: IsEvent e => M.Map String String -> IORef (Bool, String) -> String -> String -> EventM Element e ()
submitQualitative opts ref g l = do (isDone,val) <- liftIO $ readIORef ref
                                    let submission = (QualitativeProblemDataOpts (pack g) (pack val) (toList opts))
                                    if isDone || ("exam" `inOpts` opts)
                                        then trySubmit Qualitative opts l submission isDone
                                        else message "Not quite right. Try again?"

submitNumerical :: IsEvent e => M.Map String String -> Element -> Int -> String -> String -> EventM Element e ()
submitNumerical opts input g p l = do Just ival <- liftIO $ I.getValue . castToHTMLInputElement $ input
                                      case readMaybe ival :: Maybe Int of
                                        Nothing -> message "Couldn't read the input. Try again?"
                                        Just val | val == g -> trySubmit Qualitative opts l (QualitativeNumericalData (pack p) val (toList opts)) True
                                        Just val | "exam" `inOpts` opts -> trySubmit Qualitative opts l (QualitativeNumericalData (pack p) val (toList opts)) False
                                        _ -> message "Not quite right. Try again?"

submitEssay :: IsEvent e => M.Map String String -> Element -> String -> String -> EventM HTMLTextAreaElement e ()
submitEssay opts text g l = do manswer <- T.getValue . castToHTMLTextAreaElement $ text
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

createNumerical :: Document -> Element -> Element -> M.Map String String -> IO ()
createNumerical w i o opts = case (M.lookup "goal" opts >>= getGoal, M.lookup "problem" opts )  of
    (Just g, Just p) -> do
        setInnerHTML i (Just p)
        bw <- createButtonWrapper w o
        Just input <- createElement w (Just "input")
        appendChild o (Just input)
        if "check" `inOpts` opts then do
              bt2 <- questionButton w "Check"
              appendChild bw (Just bt2)
              checkIt <- newListener $ do 
                              Just ival <- liftIO $ I.getValue . castToHTMLInputElement $ input
                              case readMaybe ival :: Maybe Int of
                                  Nothing -> message "Couldn't read the input. Try again?"
                                  Just v | v == g -> message "Correct!"
                                  _ -> message "Not quite right. Try again?"
              addListener bt2 click checkIt False                
        else return ()
        case M.lookup "submission" opts of
            Just s | Prelude.take 7 s == "saveAs:" -> do
                let l = Prelude.drop 7 s
                bt1 <- doneButton w "Submit"
                appendChild bw (Just bt1)
                submit <- newListener $ submitNumerical opts input g p l
                addListener bt1 click submit False                
            _ -> return ()
    _ -> print "numerical answer was missing an option"

    where getGoal = if "nocipher" `inOpts` opts then readMaybe else readMaybe . simpleDecipher . read

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
