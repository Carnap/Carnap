{-#LANGUAGE FlexibleContexts, RankNTypes #-}
module Carnap.GHCJS.Action.QualitativeProblem (qualitativeProblemAction) where

import Lib
import Carnap.GHCJS.SharedFunctions (simpleHash, simpleDecipher)
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.HTMLTextAreaElement as T (setValue, getValue) 
import GHCJS.DOM.HTMLInputElement as I (getValue, setValue, getChecked) 
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.Window (confirm)
import GHCJS.DOM.Node (appendChild, getParentNode, getParentElement)
import GHCJS.DOM.Document (createElement)
import GHCJS.DOM.EventM (newListener, addListener, EventM)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (newIORef, IORef, readIORef, writeIORef)
import Data.Map as M
import Data.Hashable
import Data.Maybe
import Data.Text (pack)
import System.Random (randomIO)
import Text.Read (readMaybe)

qualitativeProblemAction :: IO ()
qualitativeProblemAction = initElements getQualitativeProblems activateQualitativeProblem

getQualitativeProblems :: Document -> HTMLElement -> IO [Maybe (Element, Element, M.Map String String)]
getQualitativeProblems d = genInOutElts d "div" "div" "qualitative"

activateQualitativeProblem :: Document -> Maybe (Element, Element, M.Map String String) -> IO ()
activateQualitativeProblem w (Just (i,o,opts)) = do
        case M.lookup "qualitativetype" opts of
            Just "multiplechoice" -> createMultipleChoice w i o opts
            Just "multipleselection" -> createMultipleSelection w i o opts
            Just "shortanswer" -> createShortAnswer w i o opts
            Just "numerical" -> createNumerical w i o opts
            _  -> return ()

submitQualitative :: IsEvent e => Document -> M.Map String String -> Element -> IORef (Bool, String) -> String -> String -> EventM Element e ()
submitQualitative w opts wrap ref g l = do 
       (isDone,val) <- liftIO $ readIORef ref
       let submission = (QualitativeProblemDataOpts (pack g) (pack val) (toList opts))
           isExam = "exam" `inOpts` opts
       if isExam then trySubmit w Qualitative opts l submission isDone 
                 else if isDone then trySubmit w Qualitative opts l submission isDone >> setSuccess w wrap
                                else message "Not quite right. Try again?" >> setFailure w wrap

submitQualitativeSelection :: IsEvent e => Document -> M.Map String String -> Element -> IORef (Bool, Map String Bool) -> String -> String -> EventM Element e ()
submitQualitativeSelection w opts wrap ref g l = do 
       (isDone,val) <- liftIO $ readIORef ref
       let submission = (QualitativeMultipleSelection (pack g) (toList val) (toList opts))
           isExam = "exam" `inOpts` opts
       if isExam then trySubmit w Qualitative opts l submission isDone 
                 else if isDone then trySubmit w Qualitative opts l submission isDone >> setSuccess w wrap
                                else message "Not quite right. Try again?" >> setFailure w wrap

submitNumerical :: IsEvent e => Document -> M.Map String String -> Element -> Element -> Double -> String -> String -> EventM Element e ()
submitNumerical w opts wrap input g p l = do 
       Just ival <- liftIO $ I.getValue . castToHTMLInputElement $ input
       case readNumeric ival of
         Nothing -> message "Couldn't read the input. Try again?"
         Just val | "exam" `inOpts` opts -> trySubmit w Qualitative opts l (QualitativeNumericalData (pack p) val (toList opts)) (val == g)
         Just val | val == g -> trySubmit w Qualitative opts l (QualitativeNumericalData (pack p) val (toList opts)) True >> setSuccess w wrap
         _ -> message "Not quite right. Try again?" >> setFailure w wrap

submitEssay :: IsEvent e => Document -> M.Map String String -> Element -> Element -> String -> String -> EventM HTMLTextAreaElement e ()
submitEssay w opts wrap text g l = do 
       manswer <- T.getValue . castToHTMLTextAreaElement $ text
       let credit = M.lookup "give-credit" opts
       case (manswer,credit) of 
            (Just answer,Just "onSubmission") -> trySubmit w Qualitative opts l (QualitativeProblemDataOpts (pack g) (pack answer) (toList opts)) True >> setSuccess w wrap
            (Just answer,_) -> trySubmit w Qualitative opts l (QualitativeProblemDataOpts (pack g) (pack answer) (toList opts)) False >> setSuccess w wrap
            (Nothing,_) -> message "It doesn't look like an answer has been written"

createMultipleSelection :: Document -> Element -> Element -> M.Map String String -> IO ()
createMultipleSelection w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        ref <- newIORef (False,mempty)
        setInnerHTML i (Just g)
        Just wrap <- getParentElement i
        bw <- createButtonWrapper w o
        let submit = submitQualitativeSelection w opts wrap ref g
        btStatus <- createSubmitButton w bw submit opts
        if "check" `inOpts` opts then addChecker w bw wrap ref else return ()
        let choices = maybe [] lines $ M.lookup "content" opts
            labeledChoices = zip3 (Prelude.map (getLabel opts) choices) 
                                  (Prelude.map (isGood opts) choices) 
                                  (Prelude.map (isChecked opts) choices)
        tag <- show <$> (randomIO :: IO Int)
        boxes <- mapM (toCheckbox (g ++ "-" ++ tag) ref) labeledChoices
        Just form <- createElement w (Just "form")
        appendChild o (Just form)
        mapM_ (appendChild form . Just . fst) boxes
        doOnce o change False $ liftIO $ btStatus Edited
        return ()
    where updateRef ref (s,b,c) = do
               (_,m) <- readIORef ref
               let m' = insert s (b == c) m
                   v' = M.foldr (&&) True m'
               writeIORef ref (v',m')

          toCheckbox g ref (s,b,c) = do 
               Just input <- createElement w (Just "input")
               Just label <- createElement w (Just "label")
               Just wrapper <- createElement w (Just "div")
               tag <- show <$> (randomIO :: IO Int)
               let theId = g ++ "-" ++ s ++ "-" ++ show tag
               updateRef ref (s,b,c)
               mapM (uncurry $ setAttribute input) $
                     [ ("type","checkbox")
                     , ("name", g)
                     , ("id", theId)
                     ] ++ if c then [("checked","checked")] else []
               setInnerHTML label (Just s)
               update <- newListener $ do isChecked <- liftIO $ getChecked $ castToHTMLInputElement input
                                          liftIO $ updateRef ref (s,b,isChecked)
               addListener input click update False
               setAttribute label "for" theId
               appendChild wrapper (Just input)
               appendChild wrapper (Just label)
               return (wrapper, b)

createMultipleChoice :: Document -> Element -> Element -> M.Map String String -> IO ()
createMultipleChoice w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        ref <- newIORef (False,"")
        setInnerHTML i (Just g)
        Just wrap <- getParentElement i
        bw <- createButtonWrapper w o
        let submit = submitQualitative w opts wrap ref g
        btStatus <- createSubmitButton w bw submit opts
        if "check" `inOpts` opts then addChecker w bw wrap ref else return ()
        let choices = maybe [] lines $ M.lookup "content" opts
            labeledChoices = zip3 (Prelude.map (getLabel opts) choices) 
                                  (Prelude.map (isGood opts) choices) 
                                  (Prelude.map (isChecked opts) choices)

        tag <- show <$> (randomIO :: IO Int)
        radios <- mapM (toRadio (g ++ "-" ++ tag) ref) labeledChoices
        Just form <- createElement w (Just "form")
        appendChild o (Just form)
        mapM_ (appendChild form . Just . fst) radios
        doOnce o change False $ liftIO $ btStatus Edited
        return ()
        
    where toRadio g ref (s,b,c) = do 
               Just input <- createElement w (Just "input")
               Just label <- createElement w (Just "label")
               Just wrapper <- createElement w (Just "div")
               tag <- show <$> (randomIO :: IO Int)
               let theId = g ++ "-" ++ s ++ "-" ++ tag
               if c then writeIORef ref (b,s) else return ()
               mapM (uncurry $ setAttribute input) $
                     [ ("type","radio")
                     , ("name", g)
                     , ("id", theId)
                     ] ++ if c then [("checked","checked")] else []
               setInnerHTML label (Just s)
               update <- newListener $ liftIO (writeIORef ref (b,s))
               addListener input click update False
               setAttribute label "for" theId
               appendChild wrapper (Just input)
               appendChild wrapper (Just label)
               return (wrapper, b)

createNumerical :: Document -> Element -> Element -> M.Map String String -> IO ()
createNumerical w i o opts = case (M.lookup "goal" opts >>= getGoal, M.lookup "problem" opts )  of
    (Just g, Just p) -> do
        setInnerHTML i (Just p)
        bw <- createButtonWrapper w o
        Just input <- createElement w (Just "input")
        Just wrap <- getParentElement i
        appendChild o (Just input)
        case M.lookup "content" opts of
            Just t -> I.setValue (castToHTMLInputElement input) (Just t)
            _ -> return ()
        if "check" `inOpts` opts then do
              bt2 <- questionButton w "Check"
              appendChild bw (Just bt2)
              checkIt <- newListener $ liftIO $ do 
                              Just ival <- I.getValue . castToHTMLInputElement $ input
                              case readNumeric ival of
                                  Nothing -> message "Couldn't read the input. Try again?" >> setFailure w wrap
                                  Just v | v == g -> message "Correct!" >> setSuccess w wrap
                                  _ -> message "Not quite right. Try again?" >> setFailure w wrap
              addListener bt2 click checkIt False                
        else return ()
        case M.lookup "submission" opts of
            Just s | Prelude.take 7 s == "saveAs:" -> do
                let l = Prelude.drop 7 s
                bt1 <- doneButton w "Submit"
                appendChild bw (Just bt1)
                submit <- newListener $ submitNumerical w opts wrap input g p l
                addListener bt1 click submit False                
            _ -> return ()
    _ -> print "numerical answer was missing an option"

    where getGoal = if "nocipher" `inOpts` opts then readNumeric else readNumeric . simpleDecipher . read

createShortAnswer :: Document -> Element -> Element -> M.Map String String -> IO ()
createShortAnswer w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        setInnerHTML i (Just g)
        Just wrap <- getParentElement i
        bw <- createButtonWrapper w o
        Just text <- createElement w (Just "textarea")
        case M.lookup "content" opts of
            Just t -> T.setValue (castToHTMLTextAreaElement text) (Just t)
            _ -> return ()
        appendChild o (Just text)
        case M.lookup "submission" opts of
            Just s | Prelude.take 7 s == "saveAs:" -> do
                let l = Prelude.drop 7 s
                bt1 <- doneButton w "Submit"
                appendChild bw (Just bt1)
                submit <- newListener $ submitEssay w opts wrap text g l
                addListener bt1 click submit False                
            _ -> return ()
        return ()

readNumeric s = readIt ('0': dropWhile (== ' ') s)
    where readIt s' = case readMaybe s' :: Maybe Double of
                        Just d -> Just d
                        Nothing -> asFrac $ break (== '/') s'

          asFrac (h,[]) = Nothing
          asFrac (h,t) | readMaybe (tail t) == Just (0 :: Int) = Nothing --no dividing by zero please
                       | otherwise = fromRational <$> maybeRational (h ++ " % " ++ tail t)

          maybeRational = readMaybe :: String -> Maybe Rational

getLabel :: M.Map String String -> String -> String
getLabel opts s = if "nocipher" `inOpts` opts
                    then dropWhile (`elem` "+-*") s
                    else case readMaybe s :: Maybe (Int, String) of
                          Just (_,s') -> s'
                          Nothing -> "indecipherable label"

isGood :: M.Map String String -> String -> Bool
isGood opts s = if "nocipher" `inOpts` opts
                  then case s of ('*':_) -> True; ('+':_) -> True; _ -> False
                  else case readMaybe s :: Maybe (Int, String) of
                         Just (h,s') -> h `elem` [simpleHash ('*':s'), simpleHash ('+':s')]
                         Nothing -> False

isChecked :: M.Map String String -> String -> Bool
isChecked opts s = if "nocipher" `inOpts` opts
                     then case s of ('-':_) -> True; ('+':_) -> True; _ -> False
                     else case readMaybe s :: Maybe (Int, String) of
                            Just (h,s') -> h `elem` [simpleHash ('-':s'), simpleHash ('+':s')]
                            Nothing -> False

addChecker :: Document -> Element -> Element -> IORef (Bool,a) -> IO ()
addChecker w bw wrap ref = do 
      bt2 <- questionButton w "Check"
      appendChild bw (Just bt2)
      checkIt <- newListener $ liftIO $ do 
                      (isDone,_) <- readIORef ref
                      if isDone 
                          then message "Correct!" >> setSuccess w wrap
                          else message "Not quite right. Try again?" >> setFailure w wrap
      addListener bt2 click checkIt False
