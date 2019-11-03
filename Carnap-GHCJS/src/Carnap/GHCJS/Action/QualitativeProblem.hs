{-#LANGUAGE FlexibleContexts, RankNTypes #-}
module Carnap.GHCJS.Action.QualitativeProblem (qualitativeProblemAction) where

import Lib
import Carnap.GHCJS.SharedFunctions (simpleHash)
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.Node (appendChild, getParentNode)
import GHCJS.DOM.Document (createElement)
import GHCJS.DOM.EventM (newListener, addListener, EventM)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (newIORef, IORef, readIORef, writeIORef)
import qualified Data.Map as M
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
            --Just "shortanswer" -> createShortAnswer w i o opts
            _  -> return ()

submitQualitative :: M.Map String String -> IORef (Bool, String) -> String -> String -> IO ()
submitQualitative opts ref g l = do (isDone,val) <- readIORef ref
                                    if isDone 
                                        then trySubmit Qualitative opts l (ProblemContent (pack g)) True
                                        else message "Not quite right. Try again?"

createMultipleChoice :: Document -> Element -> Element -> M.Map String String -> IO ()
createMultipleChoice w i o opts = case M.lookup "goal" opts of
    Nothing -> return ()
    Just g -> do
        ref <- newIORef (False,"")
        setInnerHTML i (Just g)
        createSubmitButton w (submitQualitative opts ref g) opts o
        let choices = maybe [] lines $ M.lookup "content" opts
            labeledChoices = zip (Prelude.map getLabel choices) (Prelude.map isGood choices)
        radios <- mapM (toRadio g ref) labeledChoices
        mapM_ (appendChild o . Just . fst) radios
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


