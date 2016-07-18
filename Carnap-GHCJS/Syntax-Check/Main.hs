{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Main where

import Lib
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
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
--
--because other modules in Lib are imported from ghcjs-base, ghc-mod will
--not work anyway.
--
--import GHCJS.DOM.Types
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, getValue, setValue)
import GHCJS.DOM.Document (Document,createElement, getBody)
import GHCJS.DOM.Node (appendChild)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

main :: IO ()
main = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               --XXX:this next line is ugly, to put it mildly. It'd be nice
               --if there was a better way to remove extraneous quotes, or
               --if the ToJSVal instance for Aeson was better beheaved
               sendJSON ("hello","hello")
               (Just b) <- getBody dom
               mcheckers <- getCheckers b
               mapM_ (activateChecker dom) mcheckers

echoTo :: IsElement element => (String -> String) -> element -> EventM HTMLInputElement KeyboardEvent ()
echoTo f o = do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                mv <- getValue t
                case mv of 
                    Nothing -> return ()
                    Just v -> liftIO $ setInnerHTML o (fmap f mv)


tryMatch :: Element -> IORef (PureForm,[PureForm], Tree PureForm) -> Document -> EventM HTMLInputElement KeyboardEvent ()
tryMatch o ref w = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                                (Just ival)  <- getValue t
                                (f,forms,ft) <- liftIO $ readIORef ref
                                setValue t (Just "")
                                case forms of
                                    [] -> setInnerHTML o (Just "success!")
                                    x:xs -> case matchMC ival x of
                                        Right b -> if b then do
                                            case children x of 
                                                 [] -> shorten x xs
                                                 children -> updateGoal x (children ++ xs)
                                            else resetGoal
                                        Left e -> case children x of
                                               [] -> shorten x xs
                                               _ -> return ()
        where updateGoal x xs = liftIO $ do modifyIORef ref (_2 .~ xs)
                                            modifyIORef ref (_3 %~ dev x)
                                            (_,_,t) <- readIORef ref
                                            redraw (head xs) t
              shorten x xs = case xs of [] -> liftIO $ setInnerHTML o (Just "success!") 
                                        _  -> updateGoal x xs
              resetGoal = do (f,_,_) <- liftIO $ readIORef ref
                             liftIO $ writeIORef ref (f, [f], T.Node f [])
                             setInnerHTML o (Just $ show f)
              dev x = adjustFirstMatching leaves (== T.Node x []) dev'
              dev' (T.Node f _) = T.Node f (map nodify $ children f)
              nodify x = T.Node x []
              redraw x t = do setInnerHTML o (Just "")
                              let t' = fmap (\y -> (y, "")) t
                              let t'' = adjustFirstMatching leaves (== T.Node (x, "") []) (const (T.Node (x, "target") [])) $ t'
                              te <- treeToUl w t''
                              ul@(Just ul') <- createElement w (Just "ul")
                              appendChild ul' (Just te)
                              appendChild o ul
                              return ()

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
activateChecker _ Nothing  = return ()
activateChecker w (Just (i,o,classes))
                | "echo" `elem` classes  = do echo <- newListener $ echoTo (tryParse purePropFormulaParser) o
                                              addListener i keyUp echo False
                | "match" `elem` classes = do Just ohtml <- getInnerHTML o
                                              let (Right f) = parse purePropFormulaParser "" ohtml
                                              ref <- newIORef (f,[f], T.Node f [])
                                              match <- newListener $ tryMatch o ref w
                                              addListener i keyUp match False
                | otherwise = return () 
activateChecker _ _ = Prelude.error "impossible"
