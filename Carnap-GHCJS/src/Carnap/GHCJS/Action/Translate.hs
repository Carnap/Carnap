{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}
module Carnap.GHCJS.Action.Translate (translateAction) where

import Lib
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Core.Data.Optics (genChildren)
import Carnap.Core.Data.Types (FixLang, Form, BoundVars, FirstOrderLex)
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Syntax (PureFirstOrderLexWith)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Languages.PureFirstOrder.Parser (folFormulaParser)
import Carnap.Languages.PureFirstOrder.Util (toDenex, isPNF, pnfEquiv)
import Carnap.Languages.PurePropositional.Parser (purePropFormulaParser,standardLetters)
import Carnap.Languages.PurePropositional.Util (isEquivTo, isDNF, isCNF, HasLiterals(..))
import Carnap.Languages.Util.LanguageClasses
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.SharedFunctions
import Data.IORef
import qualified Data.Map as M
import Data.Text (pack,Text)
import Text.Parsec 
import Text.Read (readMaybe)
import Data.Maybe (catMaybes)
import GHCJS.DOM
import GHCJS.DOM.Types hiding (Text)
import GHCJS.DOM.Element hiding (drop)
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, setValue, getValue,castToHTMLInputElement)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Lens (Prism', toListOf, cosmos, Fold, filtered)

translateAction :: IO ()
translateAction = initElements getTranslates activateTranslate

getTranslates :: IsElement self => Document -> self -> IO [Maybe (Element, Element, M.Map String String)]
getTranslates d = genInOutElts d "input" "div" "translate"

type BinaryTest lex sem = FixLang lex sem -> FixLang lex sem -> Bool

type UnaryTest lex sem = FixLang lex sem -> Maybe String

activateTranslate :: Document -> Maybe (Element, Element, M.Map String String) -> IO ()
activateTranslate w (Just (i,o,opts)) = do
        case (M.lookup "transtype" opts, M.lookup "system" opts) of
            (Just "prop", mparser) -> activateWith formParser propChecker (propTests testlist)
                where formParser = case mparser >>= ofPropSys ndParseForm of
                                       Nothing -> purePropFormulaParser standardLetters
                                       Just theParser -> theParser
            (Just "first-order", mparser) -> activateWith formParser folChecker (folTests testlist)
                where formParser = case mparser >>= ofFOLSys ndParseForm of
                                       Nothing -> folFormulaParser
                                       Just theParser -> theParser 
            _ -> return ()
    where testlist = case M.lookup "tests" opts of Just s -> words s; Nothing -> []
          optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          getGoal = if "nocipher" `elem` optlist then id else simpleDecipher . read
          activateWith parser checker tests =
              case (M.lookup "goal" opts, M.lookup "content" opts, M.lookup "problem" opts) of
                  (Just g, Just content, Just problem) ->
                    case parse (parser `sepBy` (spaces >> char ',' >> spaces) <* eof) "" (getGoal g) of
                      (Right fs) -> do 
                           bw <- createButtonWrapper w o
                           ref <- newIORef False
                           let submit = submitTrans opts i ref fs parser checker tests
                           btStatus <- createSubmitButton w bw submit opts
                           setValue (castToHTMLInputElement i) (Just content)
                           doOnce i input False $ liftIO $ btStatus Edited
                           setInnerHTML o (Just problem)
                           mpar@(Just par) <- getParentNode o               
                           insertBefore par (Just bw) (Just o)
                           translate <- newListener $ tryTrans parser checker tests o ref fs
                           if "nocheck" `elem` optlist 
                               then return ()
                               else addListener i keyUp translate False                  
                      (Left e) -> setInnerHTML o (Just $ show e)
                  _ -> print "translation was missing an option"
activateChecker _ Nothing  = return ()

folTests :: forall lex . 
     ( FirstOrderLex (lex (FixLang (PureFirstOrderLexWith lex)))
     , HasLiterals (PureFirstOrderLexWith lex) Bool
     ) => [String] -> UnaryTest (PureFirstOrderLexWith lex) (Form Bool)
folTests testlist f = case catMaybes $ map ($ f) theTests of 
                            [] -> Nothing
                            s:ss -> Just $ foldl (\x y -> x ++ ", and " ++ y) s ss
    where theTests = map toTest testlist ++ [propTests testlist]
          toTest "PNF" submission | isPNF submission = Nothing
                                  | otherwise = Just "this submission is not in Prenex Normal Form"
          toTest _ _ = Nothing

propTests :: forall sem lex . 
    ( PrismBooleanConnLex lex sem
    , PrismBooleanConst lex sem
    , HasLiterals lex sem
    , BoundVars lex
    ) => [String] -> UnaryTest lex (Form sem)
propTests testlist f = case catMaybes $ map ($ f) theTests of 
                            [] -> Nothing
                            s:ss -> Just $ foldl (\x y -> x ++ ", and " ++ y) s ss
    where theTests = map toTest testlist
          toTest "CNF" submission | isCNF submission = Nothing
                                  | otherwise = Just "this submission is not in Conjunctive Normal Form"
          toTest "DNF" submission | isDNF submission = Nothing
                                  | otherwise = Just "this submission is not in Disjunctive Normal Form"
          toTest max submission   | take 7 max == "maxNeg:"   = maxWith 7 max (retype _not') "negations" submission
                                  | take 7 max == "maxAnd:"   = maxWith 7 max (retype _and') "conjunctions" submission
                                  | take 7 max == "maxIff:"   = maxWith 7 max (retype _iff') "biconditionals" submission
                                  | take 6 max == "maxIf:"    = maxWith 6 max (retype _if') "conditionals" submission
                                  | take 6 max == "maxOr:"    = maxWith 6 max (retype _or') "disjunctions" submission
                                  | take 7 max == "maxCon:"   = maxWith 7 max (cosmos . _nonAtom) "connectives" submission
                                  | take 8 max == "maxAtom:"  = maxWith 8 max (cosmos . _atom) "atomic sentences" submission
                                  | take 9 max == "maxFalse:" = maxWith 9 max (cosmos . _falsum) "falsity constants" submission
          toTest _ _ = Nothing

          countFold p = length . toListOf p
          retype p = genChildren . cosmos . p

          maxWith len tag p label submission = 
                do n <- readMaybe (drop len tag)
                   let occurs = countFold p submission
                   if occurs > n 
                   then Just $ "you have " ++ show occurs ++ " " ++ label ++ ", but should have "
                             ++ show n ++ " at most"
                   else Nothing

          _nonAtom :: Fold (FixLang lex (Form sem)) (FixLang lex (Form sem))
          _nonAtom = filtered (not . isAtom)

          _not' :: Prism' (FixLang lex (Form sem -> Form sem)) ()
          _not' = _not

          _atom :: Fold (FixLang lex (Form sem)) (FixLang lex (Form sem))
          _atom = filtered isAtom

          _if' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _if' = _if

          _or' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _or' = _or

          _iff' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _iff' = _iff 

          _and' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _and' = _and 

tryTrans :: Eq (FixLang lex sem) => 
    Parsec String () (FixLang lex sem) -> BinaryTest lex sem -> UnaryTest lex sem
    -> Element -> IORef Bool -> [FixLang lex sem] -> EventM HTMLInputElement KeyboardEvent ()
tryTrans parser equiv tests o ref fs = onEnter $ 
                do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                   (Just ival)  <- getValue t
                   case parse (spaces *> parser <* eof) "" ival of
                         Right f -> liftIO $ case tests f of
                                                  Nothing -> checkForm f
                                                  Just msg -> writeIORef ref False >> message ("Looks like " ++ msg ++ ".")
                         Left e -> message "Sorry, try again---that formula isn't gramatical."
   where checkForm f' 
            | f' `elem` fs = do message "perfect match!"
                                writeIORef ref True
                                setAttribute o "class" "output success"
            | any (\f -> f' `equiv` f) fs = do message "Logically equivalent to a standard translation"
                                               writeIORef ref True
                                               setAttribute o "class" "output success"
            | otherwise = do writeIORef ref False >> message "Not quite. Try again!"
                             setAttribute o "class" "output"

submitTrans opts i ref fs parser checker tests l = 
        do isFinished <- liftIO $ readIORef ref
           if isFinished
           then trySubmit Translation opts l (ProblemContent (pack $ show fs)) True
           else if ("exam" `inOpts` opts) || ("nocheck" `inOpts` opts) 
                then do 
                    (Just v) <- getValue (castToHTMLInputElement i)
                    case parse (spaces *> parser <* eof) "" v of
                        Right f' | tests f' == Nothing && any (\f -> checker f f') fs -> trySubmit Translation opts l (ProblemContent (serialize fs)) True
                        Left _ | "checksyntax" `inOpts` opts -> message "Can't read this. Please double check syntax before submitting."
                        _ | "exam" `inOpts` opts -> trySubmit Translation opts l (TranslationDataOpts (serialize fs) (pack v) (M.toList opts)) False
                        _ -> message "something is wrong... try again?"
                else message "not yet finished (remember to press return to check your work before submitting!)"
    where serialize :: Show a => [a] -> Text
          serialize = pack . tail . init . show --we drop the list brackets

propChecker f g = f == g || f `isEquivTo` g

folChecker f g = f == g || toDenex f `pnfEquiv` toDenex g
