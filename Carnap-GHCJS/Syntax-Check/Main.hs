{-# LANGUAGE FlexibleContexts #-}
module Main where

import Lib
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
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
import Control.Monad.IO.Class (liftIO)

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

tryParse s = unPack $ parse purePropFormulaParser "" s 
    where unPack (Right s) = show s
          unPack (Left e)  = show e

tryMatch :: Element -> EventM HTMLInputElement KeyboardEvent ()
tryMatch o = do (Just t) <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
                (Just ival)  <- getValue t
                (Just ohtml) <- getInnerHTML o
                case matchMC ival ohtml of
                    Right b -> if b then (liftIO $ putStrLn "success!") else (liftIO $ putStrLn "failure..")
                    Left e -> liftIO $ putStrLn (show e)


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

matchMC :: String -> String -> Either ParseError Bool
matchMC c f = do con <- parse parseConnective "" c
                 fm  <- parse purePropFormulaParser "" f
                 mc  <- mcOf fm
                 return $ con == mc
        where mcOf :: (Schematizable (f (FixLang f)), CopulaSchema (FixLang f)) => FixLang f a -> Either ParseError String
              mcOf (h :!$: t) = mcOf h
              mcOf h = Right (show h)

listOfNodesByClass :: IsElement self => self -> String -> IO [Maybe Node]
listOfNodesByClass elt c = do mnl <- getElementsByClassName elt c
                              case mnl of 
                                Nothing -> return []
                                Just nl -> do l <- getLength nl
                                              mapM (item nl) [0 .. l-1]

getCheckers :: IsElement self => self -> IO [Maybe (Element, Element, [String])]
getCheckers b = do lspans <- listOfNodesByClass b "synchecker"
                   mapM extractCheckers lspans
        where extractCheckers Nothing = return Nothing
              extractCheckers (Just span) = do let espan = castToElement span
                                               mi <- getFirstElementChild espan
                                               cn <- getClassName espan
                                               case mi of
                                                   Just i -> do mo <- getNextElementSibling i
                                                                case mo of (Just o) -> return $ Just (i,o,words cn)
                                                                           Nothing -> return Nothing
                                                   Nothing -> return Nothing

activateChecker :: Maybe (Element, Element,[String]) -> IO ()
activateChecker Nothing    = return ()
activateChecker (Just (i,o,classes))
                | "echo" `elem` classes  = do echo <- newListener $ echoTo tryParse o
                                              addListener i keyUp echo False
                | "match" `elem` classes = do match <- newListener $ tryMatch o
                                              addListener i keyUp match False
                | otherwise = return () 
activateChecker _ = Prelude.error "impossible"
