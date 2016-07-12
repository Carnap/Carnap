{-# LANGUAGE FlexibleContexts #-}
module Main where

import Lib
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Data.IORef
import Data.List (intercalate)
import Control.Lens
import Control.Lens.Plated (children)
import Text.Parsec
import Text.Parsec.Error
import Text.Parsec.Pos
import GHCJS.DOM
import GHCJS.DOM.Element
--the import below is here to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM.Types
import GHCJS.DOM.HTMLInputElement
import GHCJS.DOM.Document (createElement, getBody)
import GHCJS.DOM.Node
import GHCJS.DOM.NodeList
import GHCJS.DOM.Event
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import GHCJS.DOM.EventTarget
import Control.Monad.IO.Class (MonadIO, liftIO)

main :: IO ()
main = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               (Just b) <- getBody dom
               mcheckers <- getCheckers b
               mapM_ activateChecker mcheckers

echoTo :: IsElement element => (String -> String) -> element -> EventM HTMLInputElement KeyboardEvent ()
echoTo f o = do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                mv <- getValue t
                case mv of 
                    Nothing -> return ()
                    Just v -> liftIO $ setInnerHTML o (fmap f mv)


tryMatch :: Element -> IORef (PureForm,[PureForm]) -> EventM HTMLInputElement KeyboardEvent ()
tryMatch o ref = onEnter $ do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                              (Just ival)  <- getValue t
                              (f,forms) <- liftIO $ readIORef ref
                              case forms of
                                  [] -> setInnerHTML o (Just "success!")
                                  x:xs -> case matchMC ival x of
                                      Right b -> if b then do
                                          case children x of 
                                               [] -> shorten xs
                                               children -> updateGoal (children ++ xs)
                                          else resetGoal
                                      Left e -> case children x of
                                             [] -> shorten xs
                                             _ -> return ()
        where updateGoal xs = do liftIO $ modifyIORef ref (_2 .~ xs)
                                 setInnerHTML o (Just $ intercalate " " $ map show xs)
              shorten xs = case xs of [] -> liftIO $ setInnerHTML o (Just "success!") 
                                      _  -> updateGoal xs
              resetGoal = do (f,xs) <- liftIO $ readIORef ref
                             liftIO $ writeIORef ref (f, [f])
                             setInnerHTML o (Just $ show f)

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

activateChecker :: Maybe (Element, Element,[String]) -> IO ()
activateChecker Nothing    = return ()
activateChecker (Just (i,o,classes))
                | "echo" `elem` classes  = do echo <- newListener $ echoTo (tryParse purePropFormulaParser) o
                                              addListener i keyUp echo False
                | "match" `elem` classes = do Just ohtml <- getInnerHTML o
                                              let (Right f) = parse purePropFormulaParser "" ohtml
                                              ref <- newIORef (f,[f])
                                              match <- newListener $ tryMatch o ref
                                              addListener i keyUp match False
                | otherwise = return () 
activateChecker _ = Prelude.error "impossible"

--------------------------------------------------------
--Functions that should go in a library
--------------------------------------------------------
--

onEnter :: EventM HTMLInputElement KeyboardEvent () ->  EventM HTMLInputElement KeyboardEvent ()
onEnter action = do kbe      <- event
                    id       <- getKeyIdentifier kbe
                    if id == "Enter" then do action
                                     else return ()

clearInput :: (MonadIO m) => HTMLInputElement -> m ()
clearInput i = setValue i (Just "")


--XXX: one might also want to include a "mutable lens" or "mutable traversal"
--kind of thing: http://stackoverflow.com/questions/18794745/can-i-make-a-lens-with-a-monad-constraint
getListOfElementsByClass :: IsElement self => self -> String -> IO [Maybe Element]
getListOfElementsByClass elt c = do mnl <- getElementsByClassName elt c
                                    case mnl of 
                                        Nothing -> return []
                                        Just nl -> do l <- getLength nl
                                                      mapM ((fmap . fmap) castToElement . item nl) [0 .. l-1]

tryParse p s = unPack $ parse p "" s 
    where unPack (Right s) = show s
          unPack (Left e)  = show e
