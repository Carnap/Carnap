{-# LANGUAGE RankNTypes, FlexibleContexts, DeriveDataTypeable, CPP, JavaScriptFFI #-}
module Lib
    ( sendJSON, onEnter, clearInput, getListOfElementsByClass, tryParse, treeToElement, treeToUl,listToUl, formToTree, leaves, adjustFirstMatching, decodeHtml
    ) where

import Data.Aeson
import Data.Tree as T
import Text.Parsec
import Text.StringLike
import Text.HTML.TagSoup as TS
import Control.Lens
import Control.Lens.Plated (children)
import Control.Monad.State
--The following three imports come from ghcjs-base, and break ghc-mod
#ifdef __GHCJS__
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
--the import below required to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLInputElement
import GHCJS.DOM.Document (createElement, getBody)
import GHCJS.DOM.Node
import GHCJS.DOM.NodeList
import GHCJS.DOM.Event
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import GHCJS.DOM.EventTarget

--------------------------------------------------------
--1. Utility Functions
--------------------------------------------------------

--------------------------------------------------------
--1.1 Events
--------------------------------------------------------

onEnter :: EventM HTMLInputElement KeyboardEvent () ->  EventM HTMLInputElement KeyboardEvent ()
onEnter action = do kbe      <- event
                    id       <- getKeyIdentifier kbe
                    if id == "Enter" then do action
                                     else return ()

--------------------------------------------------------
--1.2 DOM Manipulation
--------------------------------------------------------

clearInput :: (MonadIO m) => HTMLInputElement -> m ()
clearInput i = setValue i (Just "")

--XXX: one might also want to include a "mutable lens" or "mutable traversal"
--kind of thing: http://stackoverflow.com/questions/18794745/can-i-make-a-lens-with-a-monad-constraint
getListOfElementsByClass :: IsElement self => self -> String -> IO [Maybe Element]
getListOfElementsByClass elt c = do mnl <- getElementsByClassName elt c
                                    case mnl of 
                                        Nothing -> return []
                                        Just nl -> do l <- getLength nl
                                                      if l > 0 then 
                                                          mapM ((fmap . fmap) castToElement . item nl) [0 .. l-1]
                                                      else return []

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

listToUl :: Show a => Document -> [a] -> IO Element
listToUl doc l = do elts <- mapM wrapIt l
                    (Just ul) <- createElement doc (Just "ul")
                    mapM_ (appendChild ul) elts
                    return ul
    where wrapIt e = do (Just li) <- createElement doc (Just "ul")
                        setInnerHTML li (Just $ show e)
                        return (Just li)

--------------------------------------------------------
--1.3 Encodings
--------------------------------------------------------

decodeHtml :: (StringLike s, Show s) => s -> s
decodeHtml = TS.fromTagText . head . parseTags

--------------------------------------------------------
--1.4 Optics
--------------------------------------------------------

leaves :: Traversal' (Tree a) (Tree a)
leaves f (T.Node x []) = f (T.Node x [])
leaves f (T.Node x xs) = T.Node <$> pure x <*> traverse (leaves f) xs

adjustFirstMatching :: Traversal' a b -> (b -> Bool) -> (b -> b) -> a -> a
adjustFirstMatching t pred  f x = evalState (traverseOf t adj x) True where
    adj y =  do b <- get
                if b && pred y 
                    then put False >> return (f y)
                    else return y

--------------------------------------------------------
--1.5 Carnap-Specific
--------------------------------------------------------

formToTree :: Plated a => a -> Tree a
formToTree f = T.Node f (map formToTree (children f))

--------------------------------------------------------
--2. FFI Wrappers
--------------------------------------------------------

#ifdef __GHCJS__

sendJSON :: ToJSON a => a -> (String -> IO ()) -> (String -> IO ()) -> IO ()
sendJSON x succ fail = do cb1 <- asyncCallback1 (cb succ)
                          cb2 <- asyncCallback1 (cb fail)
                          jsonCommand (toJSString . clean . encode $ x) cb1 cb2
    where clean :: Show a => a -> String
          clean = read . show 
          cb f x = do (Just s) <- fromJSVal x 
                      f s

foreign import javascript unsafe "jsonCommand($1,$2,$3)" jsonCommand :: JSString -> Callback (JSVal -> IO()) -> Callback (JSVal -> IO()) -> IO ()

#else

sendJSON :: ToJSON a => a -> (String -> IO ()) -> (String -> IO ()) -> IO ()
sendJSON = Prelude.error "sendJSON requires the GHCJS FFI"

#endif
