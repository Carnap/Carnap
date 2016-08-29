{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.Translate (translateAction) where

import Lib
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
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
import GHCJS.DOM.Window (alert)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

-- XXX: There's clearly a pattern here that could be factored out.
translateAction :: IO ()
translateAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               (Just b) <- getBody dom
               mtranslates <- getTranslates b
               case mtranslates of 
                    [] -> return ()
                    _ -> mapM_ (activateTranslate dom) mtranslates

-- XXX: also here
getTranslates :: IsElement self => self -> IO [Maybe (Element, Element, [String])]
getTranslates b = do els <- getListOfElementsByClass b "translate"
                     mapM extractTranslates els
        where extractTranslates Nothing = return Nothing
              extractTranslates (Just el) = 
                do mi <- getFirstElementChild el
                   cn <- getClassName el
                   case mi of
                       Just c1 -> do mc2 <- getNextElementSibling c1
                                     case mc2 of (Just c2) -> return $ Just (c1,c2,words cn)
                                                 Nothing -> return Nothing
                       Nothing -> return Nothing

activateTranslate :: Document -> Maybe (Element, Element,[String]) -> IO ()
activateTranslate w (Just (i,o,classes))
                | "prop" `elem` classes = 
                                 do Just ohtml <- getInnerHTML o                                           
                                    case parse formAndLabel "" (simpleCipher $ decodeHtml ohtml) of                       
                                      (Right (l,f)) -> do mbt@(Just bt) <- createElement w (Just "button")
                                                          (Just ival) <- getValue (castToHTMLInputElement i)
                                                          setInnerHTML o (Just ival :: Maybe String)
                                                          setInnerHTML bt (Just "submit solution")         
                                                          mpar@(Just par) <- getParentNode o               
                                                          insertBefore par mbt (Just o)
                                                          ref <- newIORef False
                                                          tryTrans <- newListener $ tryTrans o ref w f
                                                          (Just w') <- getDefaultView w                    
                                                          submit <- newListener $ trySubmit ref w' l f
                                                          addListener i keyUp tryTrans False                  
                                                          addListener bt click submit False                
                                      (Left e) -> print $ ohtml ++ show e                                  
                | otherwise = return () 
activateChecker _ Nothing  = return ()

tryTrans :: Element -> IORef Bool -> Document -> PureForm -> EventM HTMLInputElement KeyboardEvent ()
tryTrans o ref w f = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                                  (Just ival)  <- getValue t
                                  case parse purePropFormulaParser "" ival of
                                      Right f' -> liftIO $ checkForm f'
                                      Left e -> message "Sorry, try again---that formula isn't gramatical."
              where message s = do (Just w') <- getDefaultView w
                                   alert w' s
                    checkForm f' 
                        | f' == f = do message "perfect match!"
                                       writeIORef ref True
                                       setInnerHTML o (Just "success!")
                        | f' `isEquivTo` f = do message "Logically equivalent to the standard translation"
                                                writeIORef ref True
                                                setInnerHTML o (Just "success!")
                        | otherwise = message "Not quite. Try again!"

trySubmit ref w l f = do isFinished <- liftIO $ readIORef ref
                         if isFinished
                           then alert w "done!" --liftIO $ sendJSON (SubmitTranslation (l ++ ":" ++ show f)) loginCheck error
                           else alert w "not yet finished"
    where loginCheck c | c == "No User" = alert w "You need to log in before you can submit anything"
                       | c == "Clash"   = alert w "it appears you've already successfully submitted this problem"
                       | otherwise      = alert w $ "Submitted Translation for Exercise " ++ l
          error c = alert w ("Something has gone wrong. Here's the error: " ++ c)


formAndLabel = do label <- many (digit <|> char '.')
                  spaces
                  f <- purePropFormulaParser
                  return (label,f)
