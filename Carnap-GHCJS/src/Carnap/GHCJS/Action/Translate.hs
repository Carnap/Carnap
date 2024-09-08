{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}
module Carnap.GHCJS.Action.Translate (translateAction) where

import Lib
import Lib.FormulaTests
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Core.Data.Types (FixLang, Form, Term, BoundVars, FirstOrderLex)
import Carnap.Languages.PurePropositional.Logic (ofPropSys, ofPropTreeSys)
import Carnap.Languages.PurePropositional.Logic.KooSL (kooSLNotation)
import Carnap.Languages.ModalPropositional.Logic (ofModalPropSys)
import Carnap.Languages.PureSecondOrder.Logic (ofSecondOrderSys) 
import Carnap.Languages.SetTheory.Logic (ofSetTheorySys, ofSetTheoryTreeSys)
import Carnap.Languages.Arithmetic.Logic (ofArithmeticTreeSys)
import Carnap.Languages.HigherOrderArithmetic.Logic (ofHigherOrderArithmeticTreeSys)
import Carnap.Languages.PureFirstOrder.Syntax (PureFirstOrderLexWith)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys, ofFOLTreeSys)
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
import Control.Monad (mplus, void)
import Control.Monad.IO.Class (MonadIO, liftIO)
import GHCJS.DOM.EventM (on)
import Control.Monad.IO.Class (liftIO)
translateAction :: IO ()
translateAction = initElements getTranslates activateTranslate

getTranslates :: IsElement self => Document -> self -> IO [Maybe (Element, Element, M.Map String String)]
getTranslates d = genInOutElts d "input" "div" "translate"

activateTranslate :: Document -> Maybe (Element, Element, M.Map String String) -> IO ()
activateTranslate w (Just (i,o,opts)) = do
        case (M.lookup "transtype" opts, M.lookup "system" opts) of
            (Just "prop", mparser) -> maybe noSystem id $ ((\it -> activateWith (tbParseForm it) propChecker (propTests testlist)) `ofPropTreeSys` sys)
                                                    `mplus` Just (activateWith formParser propChecker (propTests testlist))
                where formParser = maybe (purePropFormulaParser standardLetters) id (mparser >>= ofPropSys ndParseForm)
            (Just "first-order", mparser) -> maybe noSystem id $ ((\it -> activateWith (ndParseForm it) folChecker noTests) `ofSetTheorySys` sys)
                                                         `mplus` ((\it -> activateWith (tbParseForm it) folChecker noTests) `ofSetTheoryTreeSys` sys)
                                                         `mplus` ((\it -> activateWith (tbParseForm it) folChecker noTests) `ofArithmeticTreeSys` sys)
                                                         `mplus` ((\it -> activateWith (tbParseForm it) folChecker noTests) `ofHigherOrderArithmeticTreeSys` sys)
                                                         `mplus` ((\it -> activateWith (tbParseForm it) folChecker (folTests testlist)) `ofFOLTreeSys` sys)
                                                         `mplus` Just (activateWith formParser folChecker (folTests testlist))
                where formParser = maybe folFormulaParser id (mparser >>= ofFOLSys ndParseForm)
            (Just "description", mparser) -> activateWith formParser descChecker (folTests testlist)
                where formParser = maybe descFormulaParser id (mparser >>= ofDefiniteDescSys ndParseForm)
            (Just "exact", mparser) -> maybe noSystem id $ ((\it -> activateWith (ndParseForm it) exactChecker (propTests testlist)) `ofPropSys` sys)
                                                   `mplus` ((\it -> activateWith (ndParseForm it) exactChecker (folTests testlist)) `ofFOLSys` sys)
                                                   `mplus` ((\it -> activateWith (ndParseForm it) exactChecker (folTests testlist)) `ofDefiniteDescSys` sys)
                                                   `mplus` ((\it -> activateWith (ndParseForm it) exactChecker noTests) `ofSecondOrderSys` sys)
                                                   `mplus` ((\it -> activateWith (ndParseForm it) exactChecker noTests) `ofSetTheorySys` sys)
                                                   `mplus` ((\it -> activateWith (tbParseForm it) exactChecker noTests) `ofSetTheoryTreeSys` sys)
                                                   `mplus` ((\it -> activateWith (tbParseForm it) exactChecker noTests) `ofArithmeticTreeSys` sys)
                                                   `mplus` ((\it -> activateWith (tbParseForm it) exactChecker noTests) `ofHigherOrderArithmeticTreeSys` sys)
                                                   `mplus` ((\it -> activateWith (tbParseForm it) exactChecker noTests) `ofFOLTreeSys` sys)
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

                            -- Set up continuous symbol transformation
                           void $ on (castToHTMLInputElement i) input $ do
                               Just ival <- getValue (castToHTMLInputElement i)
                               let transformedInput = kooSLNotation ival
                               setValue (castToHTMLInputElement i) (Just transformedInput)
                               liftIO $ btStatus Edited

                           bw2 <- createButtonWrapperConst w o
                           let createSymbolBtn symbol = createSymbolButton w bw2 symbol (insertSymbolClick i symbol)
                           case (M.lookup "transtype" opts) of
                                 (Just "prop") -> mapM createSymbolBtn ["~", "→", "↔", "∧", "∨"]
                                 _ -> mapM createSymbolBtn ["~", "→", "↔", "∧", "∨", "∀", "∃", "≠"]
                           symbolsPane <- createSymbolsPane w i
                            -- Get Show Symbols button
                           showSymbolsBtn <- getShowSymbolsButton w symbolsPane     
                           appendChild symbolsPane (Just bw2)

                           resetButton <- questionButton w "Reset"
                           appendChild bw (Just resetButton)
                           resetIt <- newListener $ resetAnswer i o opts
                           addListener resetButton click resetIt False

                           checkButton <- questionButton w "Check"
                           appendChild bw (Just checkButton)
                           checkIt <- newListener $ liftIO $ tryTrans_wrap w parser checker tests i ref fs
                           addListener checkButton click checkIt False

                           -- Initally set input box to empty
                           setValue (castToHTMLInputElement i) (Just "")
                           
                           doOnce i input False $ liftIO $ btStatus Edited
                           setInnerHTML o (Just problem)
                           mpar@(Just par) <- getParentNode o               
                           insertBefore par (Just bw) (Just o)
                           appendChild bw (Just showSymbolsBtn)
                           appendChild par (Just symbolsPane)
                           Just wrapper <- getParentElement o
                           return ()
                        --    setAttribute i "enterKeyHint" "go"
                        --    translate <- newListener $ tryTrans w parser checker tests wrapper ref fs
                        --    if "nocheck" `elem` optlist 
                        --        then return ()
                        --        else addListener i keyUp translate False
                      (Left e) -> setInnerHTML o (Just $ show e)
                  _ -> print "translation was missing an option"
activateChecker _ Nothing  = return ()

resetAnswer :: Element -> Element -> M.Map String String -> EventM Element MouseEvent ()
resetAnswer inputElem outputElem opts = liftIO $ do
    Just parentDiv <- getParentElement inputElem
    removeClassFromElement parentDiv "success"
    setValue (castToHTMLInputElement inputElem) (Just "")

tryTrans :: Eq (FixLang lex sem) => 
    Document -> Parsec String () (FixLang lex sem) -> BinaryTest lex sem -> UnaryTest lex sem
    -> Element -> IORef Bool -> [FixLang lex sem] -> EventM HTMLInputElement KeyboardEvent ()
tryTrans w parser equiv tests wrapper ref fs = onEnter $ 
                do Just t <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                   Just ival  <- getValue t
                   let transformedInput = kooSLNotation ival  -- Apply kooSLNotation here
                   setValue t (Just transformedInput)  -- Update the input box with the transformed input
                   case parse (spaces *> parser <* eof) "" transformedInput of
                         Right f -> liftIO $ case tests f of
                                                  Nothing -> checkForm f
                                                  Just msg -> writeIORef ref False >> message ("Looks like " ++ msg ++ ".")
                         Left e -> message "Sorry, try again---that formula isn't grammatical."
   where checkForm f' 
            | f' `elem` fs = do message "Perfect match!"
                                writeIORef ref True
                                setSuccess w wrapper
            | any (\f -> f' `equiv` f) fs = do message "Correct!"
                                               writeIORef ref True
                                               setSuccess w wrapper
            | otherwise = do message "Not quite. Try again?"
                             writeIORef ref False 
                             setFailure w wrapper

tryTrans_wrap :: Eq (FixLang lex sem) => 
    Document -> Parsec String () (FixLang lex sem) -> BinaryTest lex sem -> UnaryTest lex sem
    -> Element -> IORef Bool -> [FixLang lex sem] -> IO ()
tryTrans_wrap w parser equiv tests inputElement ref fs = do
    Just ival <- getValue (castToHTMLInputElement inputElement)
    let transformedInput = kooSLNotation ival
    setValue (castToHTMLInputElement inputElement) (Just transformedInput)
    case parse (spaces *> parser <* eof) "" transformedInput of
        Right f -> case tests f of
            Nothing -> checkForm f
            Just msg -> writeIORef ref False >> message ("Looks like " ++ msg ++ ".")
        Left e -> message "Sorry, try again---that formula isn't grammatical."
    where
        checkForm f'
            | f' `elem` fs = do 
                message "Perfect match! (Answer has not been submitted)"
                writeIORef ref True
                setSuccess w inputElement
            | any (\f -> f' `equiv` f) fs = do 
                message "Correct! (Answer has not been submitted)"
                writeIORef ref True
                setSuccess w inputElement
            | otherwise = do 
                message "Not quite. Try again?"
                writeIORef ref False
                setFailure w inputElement

submitTrans w opts i ref fs parser checker tests l =
        do isFinished <- liftIO $ readIORef ref
           (Just v) <- getValue (castToHTMLInputElement i)
           if isFinished
           then trySubmit w Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) True
           else if ("exam" `inOpts` opts) || ("nocheck" `inOpts` opts) 
                then do
                    -- liftIO $ tryTrans_wrap w parser checker tests wrapper ref fs
                    case parse (spaces *> parser <* eof) "" v of
                        Right f' | tests f' == Nothing && any (\f -> checker f f') fs -> 
                            trySubmit w Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) True
                        Left _ | "checksyntax" `inOpts` opts -> 
                            message "Can't read this. Please double check syntax before submitting."
                        _ | "exam" `inOpts` opts -> 
                            trySubmit w Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) False
                        _ -> message "Something is wrong... try again?"
                else do
                    liftIO $ tryTrans_wrap w parser checker tests i ref fs
    where serialize :: Show a => [a] -> Text
          serialize = pack . tail . init . show --we drop the list brackets

propChecker f g = f == g || f `isEquivTo` g

folChecker f g = f == g || toDenex f `pnfEquiv` toDenex g

descChecker f g = f == g || toDenex f `descEquivPNF` toDenex g

exactChecker f g = f == g