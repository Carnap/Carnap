{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Main where

import Lib
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Data.IORef
import Data.Aeson
import Data.List (intercalate)
import Data.Tree as T
import Control.Lens
import Control.Lens.Plated (children)
import Text.Parsec
import Text.Parsec.Error
import Text.Parsec.Pos
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Marshal
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
import Control.Monad.State

main :: IO ()
main = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               --XXX:this next line is ugly, to put it mildly. It'd be nice
               --if there was a better way to remove extraneous quotes, or
               --if the ToJSVal instance for Aeson was better beheaved
               jsonCommand $ toJSString (read $ show $ encode ("hello","hello") :: String)
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

treeToElement :: (a -> IO Element) -> (Element -> [Element] -> IO ()) -> Tree a -> IO Element
treeToElement f g (T.Node n []) = f n
treeToElement f g (T.Node n ts) = do r <- f n
                                     elts <- mapM (treeToElement f g) ts
                                     g r elts
                                     return r

treeToUl :: Show a => Document -> Tree (a, String) -> IO Element
treeToUl w t = treeToElement itemize listify t
    where itemize (x,c) = do s@(Just s') <- createElement w (Just "li")
                             setInnerHTML s' (Just $ show x)
                             setAttribute s' "class" c 
                             return s'
          listify x xs = do o@(Just o') <- createElement w (Just "ul")
                            mapM_ (appendChild o' . Just) xs
                            appendChild x o
                            return ()
                                     
formToTree :: Plated a => a -> Tree a
formToTree f = T.Node f (map formToTree (children f))

leaves :: Traversal' (Tree a) (Tree a)
leaves f (T.Node x []) = f (T.Node x [])
leaves f (T.Node x xs) = T.Node <$> pure x <*> traverse (leaves f) xs

adjustFirstMatching :: Traversal' a b -> (b -> Bool) -> (b -> b) -> a -> a
adjustFirstMatching t pred  f x = evalState (traverseOf t adj x) True where
    adj y =  do b <- get
                if b && pred y 
                    then put False >> return (f y)
                    else return y
