{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.Translate (translateAction) where

import Lib
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Carnap.Languages.PureFirstOrder.Syntax (PureFOLForm)
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.PurePropositional.Logic (montagueSCCalc, ofPropSys)
import Carnap.Languages.PureFirstOrder.Parser (folFormulaParser)
import Carnap.Languages.PureFirstOrder.Logic (folCalc)
import Carnap.Languages.PurePropositional.Parser (purePropFormulaParser,standardLetters)
import Carnap.Languages.PureFirstOrder.Parser (folFormulaParserRelaxed)
import Carnap.Languages.PurePropositional.Util (isEquivTo)
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.SharedFunctions
import Data.IORef
import Data.Map as M
import Data.Text (pack)
import Text.Parsec 
import GHCJS.DOM
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, setValue, getValue,castToHTMLInputElement)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

translateAction :: IO ()
translateAction = initElements getTranslates activateTranslate

getTranslates :: IsElement self => Document -> self -> IO [Maybe (Element, Element, Map String String)]
getTranslates d = genInOutElts d "input" "div" "translate"

activateTranslate :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateTranslate w (Just (i,o,opts)) = do
        case (M.lookup "transtype" opts, M.lookup "system" opts) of
            (Just "prop", mparser) -> activateWith formParser (tryTrans formParser) propChecker
                where formParser = case mparser >>= ofPropSys ndParseForm of
                                       Nothing -> purePropFormulaParser standardLetters <* eof
                                       Just theParser -> theParser <* eof
            (Just "first-order", mparser) -> activateWith formParser (tryFOLTrans formParser) folChecker
                where formParser = case mparser >>= ofFOLSys ndParseForm of
                                       Nothing -> folFormulaParser <* eof
                                       Just theParser -> theParser <* eof
            _ -> return ()
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          activateWith parser translator checker =
              case (M.lookup "goal" opts, M.lookup "content" opts, M.lookup "problem" opts) of
                  (Just g, Just content, Just problem) ->
                    case parse parser "" (simpleDecipher . read $ g) of
                      (Right f) -> do 
                           bw <- buttonWrapper w
                           ref <- newIORef False
                           case M.lookup "submission" opts of
                              Just s | take 7 s == "saveAs:" -> do
                                  let l = Prelude.drop 7 s
                                  bt <- doneButton w "Submit Solution"
                                  appendChild bw (Just bt)
                                  submit <- newListener $ submitTrans opts i ref l f parser checker
                                  addListener bt click submit False                
                              _ -> return ()
                           setValue (castToHTMLInputElement i) (Just content)
                           setInnerHTML o (Just problem)
                           mpar@(Just par) <- getParentNode o               
                           insertBefore par (Just bw) (Just o)
                           translate <- newListener $ translator o ref f
                           if "nocheck" `elem` optlist 
                               then return ()
                               else addListener i keyUp translate False                  
                      (Left e) -> setInnerHTML o (Just $ show e)
                  _ -> print "translation was missing an option"
activateChecker _ Nothing  = return ()

tryTrans :: Parsec String () PureForm -> Element -> IORef Bool -> PureForm -> 
    EventM HTMLInputElement KeyboardEvent ()
tryTrans parser o ref f = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                                       (Just ival)  <- getValue t
                                       case parse (spaces *> parser) "" ival of
                                             Right f' -> liftIO $ checkForm f'
                                             Left e -> message "Sorry, try again---that formula isn't gramatical."
   where checkForm f' 
            | f' == f = do message "perfect match!"
                           writeIORef ref True
                           setInnerHTML o (Just "Success!")
            | f' `isEquivTo` f = do message "Logically equivalent to the standard translation"
                                    writeIORef ref True
                                    setInnerHTML o (Just "Success!")
            | otherwise = message "Not quite. Try again!"


tryFOLTrans :: Parsec String () PureFOLForm -> Element -> IORef Bool -> PureFOLForm -> 
    EventM HTMLInputElement KeyboardEvent ()
tryFOLTrans parser o ref f = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                                          (Just ival)  <- getValue t
                                          case parse (spaces *> parser) "" ival of
                                                 Right f' -> liftIO $ checkForm f'
                                                 Left e -> message "Sorry, try again---that formula isn't gramatical."
  where checkForm f' 
            | f' == f = do message "perfect match!"
                           writeIORef ref True
                           setInnerHTML o (Just "Success!")
            | otherwise = message "Not quite. Try again!"
            -- TODO Add FOL equivalence checking code, insofar as possible.

submitTrans opts i ref l f parser checker = 
        do isFinished <- liftIO $ readIORef ref
           if isFinished
               then trySubmit Translation opts l (ProblemContent (pack $ show f)) True
               else if ("exam" `elem` optlist) || ("nocheck" `elem` optlist)
                        then do (Just v) <- getValue (castToHTMLInputElement i)
                                case parse parser "" v of
                                    Right f' | checker f f' -> trySubmit Translation opts l (ProblemContent (pack $ show f)) True
                                    _ -> trySubmit Translation opts l (TranslationDataOpts (pack $ show f) (pack v) (toList opts)) False
                        else message "not yet finished (remember to press return to check your work before submitting!)"
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

propChecker f f' = f == f' || f `isEquivTo` f'

folChecker f f' = f == f'
