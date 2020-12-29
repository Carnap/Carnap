{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.SyntaxCheck (syntaxCheckAction) where

import Lib
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Syntax 
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.Util.LanguageClasses
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.PurePropositional.Logic
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.GHCJS.SharedTypes
import Data.IORef
import qualified Data.Map as M
import Data.Tree as T
import Data.Text (pack)
import Control.Lens
import Control.Lens.Plated (children)
import Text.Parsec
import GHCJS.DOM
import GHCJS.DOM.Element
--the import below is needed to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM.Types
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, getValue, setValue)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, getParentElement, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

syntaxCheckAction:: IO ()
syntaxCheckAction = initElements getCheckers activateChecker

-- XXX:this could be cleaner. The basic idea is that we maintain a "stage"
--in development and use the stages to match formulas in the tree with
--formulas in the todo list. The labeling makes it possible to identify
--which formula is in the queue, even when there are several
--syntactically indistinguishable formulas
tryMatch :: Element -> IORef (PureForm, [(PureForm, Int)], Tree (PureForm, Int), Int) 
            -> Document -> (PureForm -> String) -> M.Map String String 
            -> EventM HTMLInputElement KeyboardEvent ()
tryMatch o ref w sf opts = onEnter $ 
        do Just t <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
           Just ival  <- getValue t
           (f, forms, ft, stage) <- liftIO $ readIORef ref
           setValue t (Just "")
           case forms of
               [] -> liftIO $ do Just wrap1<- getParentElement o
                                 Just wrap2 <- getParentElement wrap1
                                 redraw Nothing ft
                                 setSuccess w wrap2
               x:xs -> case matchMC ival (fst x) of
                   Right b -> if b 
                       then case children (fst x) of 
                               [] -> shorten x xs stage
                               children -> updateGoal x (zip children [(stage + 1)..]) xs (stage + length children + 1)
                       else do message $ "Sorry, that's not the main connective. Try again!"
                               resetGoal
                   Left e -> case children (fst x) of
                          [] -> shorten x xs stage
                          _ -> message "what you've entered doesn't appear to be a connective"
        where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
              --updates the goal, by adding labeled formulas to the todo ist, 
              --developing the tree with those labeled formulas at the given label, and 
              --advances the stage
              updateGoal x cs xs stage = 
                    do liftIO $ modifyIORef ref (_2 .~ (cs ++ xs))
                       liftIO $ modifyIORef ref (_3 %~ dev x cs)
                       liftIO $ modifyIORef ref (_4 .~ stage)
                       (_,_,t,_) <- liftIO $ readIORef ref
                       if "parseAtoms" `elem` optlist 
                           then liftIO $ redraw (Just (head (cs ++ xs))) t
                           else case (cs ++ xs) of
                                   c:css | children (fst c) == [] -> shorten c css stage
                                   l -> liftIO $ redraw (Just (head l)) t
              shorten x xs stage = case xs of [] -> liftIO $ do Just wrap1 <- getParentElement o
                                                                Just wrap2 <- getParentElement wrap1
                                                                (_,_,t,_) <- readIORef ref
                                                                redraw Nothing t
                                                                setAttribute wrap2 "class" "success"
                                                                modifyIORef ref (_2 .~ []) 
                                              _  -> updateGoal x [] xs stage
              resetGoal = do (f,_,_,_) <- liftIO $ readIORef ref
                             liftIO $ writeIORef ref (f, [(f,0)], T.Node (f,0) [],0)
                             setInnerHTML o (Just $ sf f)
              dev x xs = adjustFirstMatching leaves (== T.Node x []) (dev' xs)
              dev' xs (T.Node x _) = T.Node x (map nodify xs)
              nodify x = T.Node x []
              redraw mx t = do setInnerHTML o (Just "")
                               let t' = fmap (\y -> (y, "")) t
                               let t'' = case mx of Just x -> adjustFirstMatching leaves (== T.Node (x, "") []) (const (T.Node (x, "target") [])) t'
                                                    Nothing -> t'
                               let t''' = fmap  (\((x,_),s) -> (x,s)) t''
                               te <- genericTreeToUl sf w t'''
                               ul@(Just ul') <- createElement w (Just "ul")
                               appendChild ul' (Just te)
                               appendChild o ul
                               return ()

parseConnective :: Monad m => ParsecT String u m String
parseConnective = choice [getAnd, getOr, getIff, getIf, getNeg]
    where tstringsToTry :: Monad m => [String] -> PurePropLanguage (Form Bool -> Form Bool -> Form Bool) -> ParsecT String u m String
          tstringsToTry l c = stringsToTry l (show c)
          getAnd = tstringsToTry ["/\\", "∧", "^", "&"] (review _and ())
          getOr  = tstringsToTry ["\\/", "∨", "v", "|"] (review _or ())
          getIf  = tstringsToTry [ "=>", "->", ">", "→"]  (review _if ())
          getIff = tstringsToTry [ "<=>",  "<->", "<>", "↔"] (review _iff ())
          getNeg = do spaces
                      _ <- string "-" <|> string "~" <|> string "¬"
                      return (show (review _not () :: PurePropLanguage (Form Bool-> Form Bool)))

matchMC :: String -> PureForm -> Either ParseError Bool
matchMC c f = do con <- parse parseConnective "" c
                 mc  <- mcOf f
                 return $ con == mc
        where mcOf :: (Schematizable (f (FixLang f)), CopulaSchema (FixLang f)) => FixLang f a -> Either ParseError String
              mcOf (h :!$: t) = mcOf h
              mcOf h = Right (show h)

getCheckers :: IsElement self => Document -> self -> IO [Maybe (Element, Element, M.Map String String)]
getCheckers d = genInOutElts d "input" "div" "synchecker"

activateChecker :: Document -> Maybe (Element, Element, M.Map String String) -> IO ()
activateChecker w (Just (i,o,opts)) =
        case M.lookup "matchtype" opts of
             (Just "match") -> activateMatchWith (rewriteWith opts . show)
             (Just "matchclean") -> activateMatchWith (rewriteWith opts . showClean)
             _ -> return () 
    where formParser = maybe (purePropFormulaParser standardLetters) id (M.lookup "system" opts >>= (ndParseForm `ofPropSys`)) 

          activateMatchWith :: (PureForm -> String) -> IO ()
          activateMatchWith sf =
              case M.lookup "goal" opts of
                  Just g ->
                    case parse (formParser <* eof) "" g of
                      (Right f) -> do 
                         bw <- createButtonWrapper w o
                         ref <- newIORef (f,[(f,0)], T.Node (f,0) [], 0)  
                         let submit = submitSyn w opts ref
                         btStatus <- createSubmitButton w bw submit opts
                         (Just tree) <- createElement w (Just "div")
                         appendChild o (Just tree)
                         setInnerHTML tree (Just $ sf f)                   
                         setAttribute tree "class" "tree"
                         mpar@(Just par) <- getParentNode o               
                         insertBefore par (Just bw) (Just o)                    
                         match <- newListener $ tryMatch tree ref w sf opts
                         (Just w') <- getDefaultView w
                         doOnce i keyUp False $ liftIO $ btStatus Edited
                         addListener i keyUp match False                  
                      (Left e) -> setInnerHTML o (Just $ show e)
                  _ -> print "syntax check was missing an option"
activateChecker _ Nothing  = return ()

submitSyn :: IsEvent e => Document -> M.Map String String -> IORef (PureForm,[(PureForm,Int)], Tree (PureForm,Int),Int) -> String -> EventM HTMLInputElement e ()
submitSyn w opts ref l = do (f,forms,_,_) <- liftIO $ readIORef ref
                            case forms of 
                               [] -> do trySubmit w SyntaxCheck opts l (ProblemContent (pack $ show f)) True
                               _  -> message "not yet finished"
