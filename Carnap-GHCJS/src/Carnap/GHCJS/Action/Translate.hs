{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.Translate (translateAction) where

import Lib
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Core.Data.Types (FixLang)
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Languages.PureFirstOrder.Parser (folFormulaParser)
import Carnap.Languages.PureFirstOrder.Util (toDenex, pnfEquiv)
import Carnap.Languages.PurePropositional.Parser (purePropFormulaParser,standardLetters)
import Carnap.Languages.PurePropositional.Util (isEquivTo)
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.SharedFunctions
import Data.IORef
import qualified Data.Map as M
import Data.Text (pack,Text)
import Text.Parsec 
import GHCJS.DOM
import GHCJS.DOM.Types hiding (Text)
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, setValue, getValue,castToHTMLInputElement)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

translateAction :: IO ()
translateAction = initElements getTranslates activateTranslate

getTranslates :: IsElement self => Document -> self -> IO [Maybe (Element, Element, M.Map String String)]
getTranslates d = genInOutElts d "input" "div" "translate"

type EquivTest lex sem = FixLang lex sem -> FixLang lex sem -> Bool

activateTranslate :: Document -> Maybe (Element, Element, M.Map String String) -> IO ()
activateTranslate w (Just (i,o,opts)) = do
        case (M.lookup "transtype" opts, M.lookup "system" opts) of
            (Just "prop", mparser) -> activateWith formParser (tryTrans formParser) propChecker
                where formParser = case mparser >>= ofPropSys ndParseForm of
                                       Nothing -> purePropFormulaParser standardLetters
                                       Just theParser -> theParser
            (Just "first-order", mparser) -> activateWith formParser (tryTrans formParser) folChecker
                where formParser = case mparser >>= ofFOLSys ndParseForm of
                                       Nothing -> folFormulaParser
                                       Just theParser -> theParser 
            _ -> return ()
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          activateWith parser translator checker =
              case (M.lookup "goal" opts, M.lookup "content" opts, M.lookup "problem" opts) of
                  (Just g, Just content, Just problem) ->
                    case parse (parser `sepBy` (spaces >> char ',' >> spaces) <* eof) "" (simpleDecipher . read $ g) of
                      (Right fs) -> do 
                           bw <- buttonWrapper w
                           ref <- newIORef False
                           case M.lookup "submission" opts of
                              Just s | take 7 s == "saveAs:" -> do
                                  let l = Prelude.drop 7 s
                                  bt <- doneButton w "Submit Solution"
                                  appendChild bw (Just bt)
                                  submit <- newListener $ submitTrans opts i ref l fs parser checker
                                  addListener bt click submit False                
                              _ -> return ()
                           setValue (castToHTMLInputElement i) (Just content)
                           setInnerHTML o (Just problem)
                           mpar@(Just par) <- getParentNode o               
                           insertBefore par (Just bw) (Just o)
                           translate <- newListener $ translator checker o ref fs
                           if "nocheck" `elem` optlist 
                               then return ()
                               else addListener i keyUp translate False                  
                      (Left e) -> setInnerHTML o (Just $ show e)
                  _ -> print "translation was missing an option"
activateChecker _ Nothing  = return ()

tryTrans :: Eq (FixLang lex sem) => Parsec String () (FixLang lex sem) -> EquivTest lex sem 
    -> Element -> IORef Bool -> [FixLang lex sem] -> EventM HTMLInputElement KeyboardEvent ()
tryTrans parser equiv o ref fs = onEnter $ 
                do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                   (Just ival)  <- getValue t
                   case parse (spaces *> parser) "" ival of
                         Right f' -> liftIO $ checkForm f'
                         Left e -> message "Sorry, try again---that formula isn't gramatical."
   where checkForm f' 
            | f' `elem` fs = do message "perfect match!"
                                writeIORef ref True
                                setInnerHTML o (Just "Success!")
            | any (\f -> f' `equiv` f) fs = do message "Logically equivalent to a standard translation"
                                               writeIORef ref True
                                               setInnerHTML o (Just "Success!")
            | otherwise = message "Not quite. Try again!"

submitTrans opts i ref l fs parser checker = 
        do isFinished <- liftIO $ readIORef ref
           if isFinished
               then trySubmit Translation opts l (ProblemContent (pack $ show fs)) True
               else if ("exam" `elem` optlist) || ("nocheck" `elem` optlist)
                        then do (Just v) <- getValue (castToHTMLInputElement i)
                                case parse parser "" v of
                                    Right f' | any (\f -> checker f f') fs -> trySubmit Translation opts l (ProblemContent (serialize fs)) True
                                    _ | "exam" `elem` optlist -> trySubmit Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) False
                                    _ -> message "something is wrong... try again?"
                        else message "not yet finished (remember to press return to check your work before submitting!)"
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          serialize :: Show a => [a] -> Text
          serialize = pack . tail . init . show --we drop the list brackets

propChecker f g = f == g || f `isEquivTo` g

folChecker f g = f == g || toDenex f `pnfEquiv` toDenex g
