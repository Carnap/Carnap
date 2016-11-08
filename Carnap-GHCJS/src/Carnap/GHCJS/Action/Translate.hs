{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.Translate (translateAction) where

import Lib
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Carnap.Languages.PureFirstOrder.Syntax (PureFOLForm)
import Carnap.Languages.PurePropositional.Parser (purePropFormulaParser)
import Carnap.Languages.PureFirstOrder.Parser (folFormulaParser)
import Carnap.Languages.PurePropositional.Util (isEquivTo)
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.SharedFunctions
import Data.IORef
import Text.Parsec 
import GHCJS.DOM
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, getValue,castToHTMLInputElement)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

translateAction :: IO ()
translateAction = initElements getTranslates activateTranslate

getTranslates :: IsElement self => self -> IO [Maybe (Element, Element, [String])]
getTranslates = getInOutElts "translate"

activateTranslate :: Document -> Maybe (Element, Element,[String]) -> IO ()
activateTranslate w (Just (i,o,classes))
                | "prop" `elem` classes = activateWith formAndLabel tryTrans
                | "first-order" `elem` classes = activateWith folFormAndLabel tryFOLTrans
                | otherwise = return ()
    where activateWith parser translator =
              do Just ohtml <- getInnerHTML o                                           
                 case parse parser "" (simpleDecipher $ read $ decodeHtml ohtml) of                       
                   (Right (l,f)) -> do mbt@(Just bt) <- createElement w (Just "button")
                                       (Just ival) <- getValue (castToHTMLInputElement i)
                                       setInnerHTML o (Just ival :: Maybe String)
                                       setInnerHTML bt (Just "submit solution")         
                                       mpar@(Just par) <- getParentNode o               
                                       insertBefore par mbt (Just o)
                                       ref <- newIORef False
                                       tryTrans <- newListener $ translator o ref f
                                       submit <- newListener $ trySubmit ref l f
                                       addListener i keyUp tryTrans False                  
                                       addListener bt click submit False                
                   (Left e) -> print $ ohtml ++ show e                                  
activateChecker _ Nothing  = return ()

tryTrans :: Element -> IORef Bool -> PureForm -> EventM HTMLInputElement KeyboardEvent ()
tryTrans o ref f = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                                (Just ival)  <- getValue t
                                case parse (spaces *> purePropFormulaParser) "" ival of
                                      Right f' -> liftIO $ checkForm f'
                                      Left e -> liftIO $ message "Sorry, try again---that formula isn't gramatical."
   where checkForm f' 
            | f' == f = do message "perfect match!"
                           writeIORef ref True
                           setInnerHTML o (Just "success!")
            | f' `isEquivTo` f = do message "Logically equivalent to the standard translation"
                                    writeIORef ref True
                                    setInnerHTML o (Just "success!")
            | otherwise = message "Not quite. Try again!"

tryFOLTrans :: Element -> IORef Bool -> PureFOLForm -> EventM HTMLInputElement KeyboardEvent ()
tryFOLTrans o ref f = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                                   (Just ival)  <- getValue t
                                   case parse (spaces *> folFormulaParser) "" ival of
                                          Right f' -> liftIO $ checkForm f'
                                          Left e -> liftIO $ message "Sorry, try again---that formula isn't gramatical."
  where checkForm f' 
            | f' == f = do message "perfect match!"
                           writeIORef ref True
                           setInnerHTML o (Just "success!")
            | otherwise = message "Not quite. Try again!"
            -- TODO Add FOL equivalence checking code, insofar as possible.

trySubmit ref l f = do isFinished <- liftIO $ readIORef ref
                       if isFinished
                         then liftIO $ sendJSON 
                                    (SubmitTranslation $ l ++ ":" ++ show f) 
                                    (loginCheck $ "Submitted Translation for Exercise " ++ l)
                                    errorPopup
                         else liftIO $ message "not yet finished (remember to press return to check your work before submitting!)"
