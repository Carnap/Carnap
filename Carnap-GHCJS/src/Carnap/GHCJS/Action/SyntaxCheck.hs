{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.SyntaxCheck (syntaxCheckAction) where

import Lib
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Util
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.GHCJS.SharedTypes
import Data.IORef
import Data.Tree as T
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
import GHCJS.DOM.Window (alert)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

syntaxCheckAction:: IO ()
syntaxCheckAction = initElements getCheckers activateChecker

echoTo :: IsElement element => (String -> String) -> element -> EventM HTMLInputElement KeyboardEvent ()
echoTo f o = do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                mv <- getValue t
                case mv of 
                    Nothing -> return ()
                    Just v -> liftIO $ setInnerHTML o (fmap f mv)

trySubmit :: IORef (PureForm,[(PureForm,Int)], Tree (PureForm,Int),Int) -> Window -> String -> EventM HTMLInputElement e ()
trySubmit ref w l = do (f,forms,_,_) <- liftIO $ readIORef ref
                       case forms of 
                          [] -> liftIO $ sendJSON 
                            (SubmitSyntaxCheck $ l ++ ":" ++ show f) 
                            (loginCheck $ "Submitted Syntax-Check for Exercise " ++ l) 
                            errorPopup
                          _  -> alert w "not yet finished"

-- XXX:this could be cleaner. The basic idea is that we maintain a "stage"
--in development and use the stages to match formulas in the tree with
--formulas in the todo list. The labeling makes it possible to identify
--which formula is in the queue, even when there are several
--indistinguishable formulas
tryMatch :: Element -> IORef (PureForm, [(PureForm, Int)], Tree (PureForm, Int), Int) -> Document -> (PureForm -> String) -> EventM HTMLInputElement KeyboardEvent ()
tryMatch o ref w sf = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                                   (Just ival)  <- getValue t
                                   (f,forms,ft, s) <- liftIO $ readIORef ref
                                   setValue t (Just "")
                                   case forms of
                                       [] -> setInnerHTML o (Just "success!")
                                       x:xs -> case matchMC ival (fst x) of
                                           Right b -> if b 
                                               then case children (fst x) of 
                                                       [] -> shorten x xs s
                                                       children -> updateGoal x (zip children [(s + 1)..]) xs (s + length children + 1)
                                               else do message $ "Sorry, that's not the main connective. Try again!"
                                                       resetGoal
                                           Left e -> case children (fst x) of
                                                  [] -> shorten x xs s
                                                  _ -> message "what you've entered doesn't appear to be a connective"
        where --updates the goal, by adding labeled formulas to the todo ist, 
              --developing the tree with those labeled formulas at the given label, and 
              --advances the stage
              updateGoal x cs xs s = liftIO $ do modifyIORef ref (_2 .~ (cs ++ xs))
                                                 modifyIORef ref (_3 %~ dev x cs)
                                                 modifyIORef ref (_4 .~ s)
                                                 (_,_,t,_) <- readIORef ref
                                                 redraw (head (cs ++ xs)) t
              shorten x xs s = case xs of [] -> liftIO $ do setInnerHTML o (Just "success!") 
                                                            modifyIORef ref (_2 .~ []) 
                                          _  -> updateGoal x [] xs s 
              resetGoal = do (f,_,_,_) <- liftIO $ readIORef ref
                             liftIO $ writeIORef ref (f, [(f,0)], T.Node (f,0) [],0)
                             setInnerHTML o (Just $ sf f)
              dev x xs = adjustFirstMatching leaves (== T.Node x []) (dev' xs)
              dev' xs (T.Node x _) = T.Node x (map nodify xs)
              nodify x = T.Node x []
              redraw x t = do setInnerHTML o (Just "")
                              let t' = fmap (\y -> (y, "")) t
                              let t'' = adjustFirstMatching leaves (== T.Node (x, "") []) (const (T.Node (x, "target") [])) t'
                              let t''' = fmap  (\((x,_),s) -> (x,s)) t''
                              te <- genericTreeToUl sf w t'''
                              ul@(Just ul') <- createElement w (Just "ul")
                              appendChild ul' (Just te)
                              appendChild o ul
                              return ()
              message s = do (Just w') <- getDefaultView w
                             alert w' s

parseConnective :: Monad m => ParsecT String u m String
parseConnective = choice [getAnd, getOr, getIff, getIf, getNeg]
    where tstringsToTry :: Monad m => [String] -> PurePropLanguage a -> ParsecT String u m String
          tstringsToTry l c = stringsToTry l (show c)
          getAnd = tstringsToTry ["/\\", "∧", "^", "&", "and"]  PAnd
          getOr  = tstringsToTry ["\\/", "∨", "v", "|", "or"]  POr
          getIf  = tstringsToTry [ "=>", "->", ">", "→", "only if"]  PIf
          getIff = tstringsToTry [ "<=>",  "<->", "<>", "↔", "if and only if"]  PIff
          getNeg = do spaces
                      _ <- string "-" <|> string "~" <|> string "¬" <|> string "not "
                      return (show (PNot :: PurePropLanguage (Form Bool-> Form Bool)))

matchMC :: String -> PureForm -> Either ParseError Bool
matchMC c f = do con <- parse parseConnective "" c
                 mc  <- mcOf f
                 return $ con == mc
        where mcOf :: (Schematizable (f (FixLang f)), CopulaSchema (FixLang f)) => FixLang f a -> Either ParseError String
              mcOf (h :!$: t) = mcOf h
              mcOf h = Right (show h)

getCheckers :: IsElement self => self -> IO [Maybe (Element, Element, [String])]
getCheckers b = do lspans <- getListOfElementsByClass b "synchecker"
                   mapM extractCheckers lspans
        where extractCheckers Nothing = return Nothing
              extractCheckers (Just span) = do mi <- getFirstElementChild span
                                               cn <- getClassName span
                                               case mi of
                                                   Just i -> do mo <- getNextElementSibling i
                                                                case mo of (Just o) -> return $ Just (i,o,words cn)
                                                                           Nothing -> return Nothing
                                                   Nothing -> return Nothing

activateChecker :: Document -> Maybe (Element, Element,[String]) -> IO ()
activateChecker w (Just (i,o,classes))
                | "echo" `elem` classes  = do echo <- newListener $ echoTo (tryParse purePropFormulaParser) o
                                              addListener i keyUp echo False
                | "match" `elem` classes = activateMatchWith show
                | "matchclean" `elem` classes = activateMatchWith showClean
                | otherwise = return () 
    where activateMatchWith :: (PureForm -> String) -> IO ()
          activateMatchWith sf = do Just ohtml <- getInnerHTML o                                           
                                    case parse formAndLabel "" (decodeHtml ohtml) of                       
                                      (Right (l,f)) -> do mbt@(Just bt) <- createElement w (Just "button") 
                                                          setInnerHTML o (Just $ sf f)                   
                                                          setInnerHTML bt (Just "submit solution")         
                                                          mpar@(Just par) <- getParentNode o               
                                                          insertBefore par mbt (Just o)                    
                                                          ref <- newIORef (f,[(f,0)], T.Node (f,0) [], 0)  
                                                          match <- newListener $ tryMatch o ref w sf
                                                          (Just w') <- getDefaultView w                    
                                                          submit <- newListener $ trySubmit ref w' l       
                                                          addListener i keyUp match False                  
                                                          addListener bt click submit False                
                                      (Left e) -> print $ ohtml ++ show e                                  
activateChecker _ Nothing  = return ()

formAndLabel = do label <- many (digit <|> char '.')
                  spaces
                  f <- purePropFormulaParser
                  return (label,f)

