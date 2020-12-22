{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}
module Carnap.GHCJS.Action.Translate (translateAction) where

import Lib
import Lib.FormulaTests
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Core.Data.Types (FixLang, Form, Term, BoundVars, FirstOrderLex)
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.ModalPropositional.Logic (ofModalPropSys)
import Carnap.Languages.PureSecondOrder.Logic (ofSecondOrderSys) 
import Carnap.Languages.SetTheory.Logic (ofSetTheorySys)
import Carnap.Languages.PureFirstOrder.Syntax (PureFirstOrderLexWith)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Languages.DefiniteDescription.Logic.Gamut
import Carnap.Languages.PureFirstOrder.Parser (folFormulaParser)
import Carnap.Languages.DefiniteDescription.Parser (descFormulaParser)
import Carnap.Languages.DefiniteDescription.Util (descEquivPNF)
import Carnap.Languages.PureFirstOrder.Util (toDenex, pnfEquiv)
import Carnap.Languages.PurePropositional.Util (isEquivTo)
import Carnap.Languages.PurePropositional.Parser (purePropFormulaParser,standardLetters)
import Carnap.Languages.Util.LanguageClasses
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.SharedFunctions
import Data.IORef
import qualified Data.Map as M
import Data.Text (pack,Text)
import Text.Parsec 
import GHCJS.DOM
import GHCJS.DOM.Types hiding (Text)
import GHCJS.DOM.Element hiding (drop)
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, setValue, getValue,castToHTMLInputElement)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore, getParentElement)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad (mplus)
import Control.Monad.IO.Class (MonadIO, liftIO)

translateAction :: IO ()
translateAction = initElements getTranslates activateTranslate

getTranslates :: IsElement self => Document -> self -> IO [Maybe (Element, Element, M.Map String String)]
getTranslates d = genInOutElts d "input" "div" "translate"

activateTranslate :: Document -> Maybe (Element, Element, M.Map String String) -> IO ()
activateTranslate w (Just (i,o,opts)) = do
        case (M.lookup "transtype" opts, M.lookup "system" opts) of
            (Just "prop", mparser) -> activateWith formParser propChecker (propTests testlist)
                where formParser = maybe (purePropFormulaParser standardLetters) id (mparser >>= ofPropSys ndParseForm)
            (Just "first-order", mparser) -> activateWith formParser folChecker (folTests testlist)
                where formParser =  maybe folFormulaParser id (mparser >>= ofFOLSys ndParseForm)
            (Just "description", mparser) -> activateWith formParser descChecker (folTests testlist)
                where formParser = maybe descFormulaParser id (mparser >>= ofDefiniteDescSys ndParseForm)
            (Just "exact", mparser) -> maybe noSystem id $  ((\it -> activateWith (ndParseForm it) exactChecker (propTests testlist)) `ofPropSys` sys)
                                                    `mplus` ((\it -> activateWith (ndParseForm it) exactChecker (folTests testlist)) `ofFOLSys` sys)
                                                    `mplus` ((\it -> activateWith (ndParseForm it) exactChecker (folTests testlist)) `ofDefiniteDescSys` sys)
                                                    `mplus` ((\it -> activateWith (ndParseForm it) exactChecker noTests) `ofSecondOrderSys` sys)
                                                    `mplus` ((\it -> activateWith (ndParseForm it) exactChecker noTests) `ofSetTheorySys` sys)
                                                    `mplus` ((\it -> activateWith (ndParseForm it) exactChecker noTests) `ofModalPropSys` sys)
            _ -> return ()
    where testlist = case M.lookup "tests" opts of Just s -> words s; Nothing -> []
          noTests _ = Nothing
          optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          getGoal = if "nocipher" `elem` optlist then id else simpleDecipher . read
          sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "prop"
          noSystem = setInnerHTML o (Just $ "Can't find a formal system named " ++ sys)
          activateWith parser checker tests =
              case (M.lookup "goal" opts, M.lookup "content" opts, M.lookup "problem" opts) of
                  (Just g, Just content, Just problem) ->
                    case parse (spaces *> parser `sepBy` (spaces >> char ',' >> spaces) <* eof) "" (getGoal g) of
                      (Right fs) -> do 
                           bw <- createButtonWrapper w o
                           ref <- newIORef False
                           let submit = submitTrans w opts i ref fs parser checker tests
                           btStatus <- createSubmitButton w bw submit opts
                           setValue (castToHTMLInputElement i) (Just content)
                           doOnce i input False $ liftIO $ btStatus Edited
                           setInnerHTML o (Just problem)
                           mpar@(Just par) <- getParentNode o               
                           insertBefore par (Just bw) (Just o)
                           Just wrapper <- getParentElement o
                           translate <- newListener $ tryTrans w parser checker tests wrapper ref fs
                           if "nocheck" `elem` optlist 
                               then return ()
                               else addListener i keyUp translate False                  
                      (Left e) -> setInnerHTML o (Just $ show e)
                  _ -> print "translation was missing an option"
activateChecker _ Nothing  = return ()


tryTrans :: Eq (FixLang lex sem) => 
    Document -> Parsec String () (FixLang lex sem) -> BinaryTest lex sem -> UnaryTest lex sem
    -> Element -> IORef Bool -> [FixLang lex sem] -> EventM HTMLInputElement KeyboardEvent ()
tryTrans w parser equiv tests wrapper ref fs = onEnter $ 
                do Just t <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                   Just ival  <- getValue t
                   case parse (spaces *> parser <* eof) "" ival of
                         Right f -> liftIO $ case tests f of
                                                  Nothing -> checkForm f
                                                  Just msg -> writeIORef ref False >> message ("Looks like " ++ msg ++ ".")
                         Left e -> message "Sorry, try again---that formula isn't gramatical."
   where checkForm f' 
            | f' `elem` fs = do message "perfect match!"
                                writeIORef ref True
                                setSuccess w wrapper
            | any (\f -> f' `equiv` f) fs = do message "Logically equivalent to a standard translation"
                                               writeIORef ref True
                                               setSuccess w wrapper
            | otherwise = do message "Not quite. Try again!"
                             writeIORef ref False 
                             setFailure w wrapper

submitTrans w opts i ref fs parser checker tests l = 
        do isFinished <- liftIO $ readIORef ref
           (Just v) <- getValue (castToHTMLInputElement i)
           if isFinished
           then trySubmit w Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) True
           else if ("exam" `inOpts` opts) || ("nocheck" `inOpts` opts) 
                then do 
                    case parse (spaces *> parser <* eof) "" v of
                        Right f' | tests f' == Nothing && any (\f -> checker f f') fs -> 
                            trySubmit w Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) True
                        Left _ | "checksyntax" `inOpts` opts -> 
                            message "Can't read this. Please double check syntax before submitting."
                        _ | "exam" `inOpts` opts -> 
                            trySubmit w Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) False
                        _ -> message "something is wrong... try again?"
                else message "not yet finished (remember to press return to check your work before submitting!)"
    where serialize :: Show a => [a] -> Text
          serialize = pack . tail . init . show --we drop the list brackets

propChecker f g = f == g || f `isEquivTo` g

folChecker f g = f == g || toDenex f `pnfEquiv` toDenex g

descChecker f g = f == g || toDenex f `descEquivPNF` toDenex g

exactChecker f g = f == g
