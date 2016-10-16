{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.TruthTable (truthTableAction) where

import Lib
import Carnap.GHCJS.SharedTypes
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses (Schematizable)
import Carnap.Languages.PurePropositional.Util (getIndicies, getValuations)
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Carnap.Languages.Util.LanguageClasses
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.Window (alert)
import GHCJS.DOM.Document (createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.EventM (newListener, addListener, EventM)
import Data.IORef (newIORef, IORef, readIORef)
import Control.Monad.IO.Class (liftIO)
import Control.Lens.Plated (children)
import Text.Parsec (parse, ParseError)

truthTableAction :: IO ()
truthTableAction = initElements getTruthTables activateTruthTables

getTruthTables :: HTMLElement -> IO [Maybe (Element, Element, [String])]
getTruthTables = getInOutElts "truthtable"

-- XXX: no dispatch on classes here yet
activateTruthTables :: Document -> Maybe (Element, Element,[String]) -> IO ()
activateTruthTables w (Just (i,o,_)) = do Just ohtml <- getInnerHTML o
                                          case parse formAndLabel "" (decodeHtml ohtml) of
                                              (Right (l,f)) -> do
                                                  mbt@(Just bt) <- createElement w (Just "button")
                                                  setInnerHTML bt (Just "submit solution")
                                                  mpar@(Just par) <- getParentNode o
                                                  insertBefore par mbt (Just o)
                                                  ref <- newIORef False
                                                  createTruthTable w f o ref
                                                  (Just w') <- getDefaultView w                    
                                                  submit <- newListener $ trySubmit ref f w' l       
                                                  addListener bt click submit False                
                                              (Left e) -> print $ ohtml ++ show e

trySubmit :: IORef Bool -> PureForm -> Window -> String -> EventM HTMLInputElement e ()
trySubmit ref f w l = do isDone <- liftIO $ readIORef ref
                         if isDone 
                            then  liftIO $ sendJSON 
                                    (SubmitTruthTable $ l ++ ":" ++ show f) 
                                    (loginCheck $ "Submitted Truth-Table for Exercise " ++ l) 
                                    errorPopup
                            else alert w "not yet finished"

createTruthTable w f o ref = do (Just table) <- createElement w (Just "table")
                                (Just thead) <- createElement w (Just "thead")
                                (Just tbody) <- createElement w (Just "tbody")
                                head <- toHead w atomIndicies orderedChildren
                                rows <- mapM toRow' valuations
                                appendChild table (Just thead)
                                appendChild table (Just tbody)
                                appendChild thead (Just head)
                                mapM (appendChild tbody . Just) (reverse rows)
                                setInnerHTML o (Just "")
                                appendChild o (Just table)
    where atomIndicies = getIndicies f
          valuations = getValuations f
          orderedChildren = traverseBPT . toBPT $ f
          toRow' = toRow w atomIndicies orderedChildren o

toRow w atomIndicies orderedChildren o v = 
        do (Just row) <- createElement w (Just "tr")
           valTds <- mapM toValTd atomIndicies
           childTds <- mapM toChildTd orderedChildren
           mapM (appendChild row . Just) (reverse valTds)
           mapM (appendChild row . Just) (childTds)
           return row
    where toValTd i = do (Just td) <- createElement w (Just "td")
                         setInnerHTML td (Just $ if v i then "T" else "F")
                         return td
          toChildTd c = do (Just td) <- createElement w (Just "td")
                           case c of
                               Left c' -> setInnerHTML td (Just "")
                               Right f -> do sel <- trueFalseOpts
                                             appendChild td (Just sel)
                                             return ()
                           return td
          trueFalseOpts = do (Just sel) <- createElement w (Just "select")
                             (Just bl)  <- createElement w (Just "option")
                             (Just tr)  <- createElement w (Just "option")
                             (Just fs)  <- createElement w (Just "option")
                             setInnerHTML bl (Just "-")
                             setInnerHTML tr (Just "T")
                             setInnerHTML fs (Just "F")
                             appendChild sel (Just bl)
                             appendChild sel (Just tr)
                             appendChild sel (Just fs)
                             return sel


toHead w atomIndicies orderedChildren = 
        do (Just row) <- createElement w (Just "tr")
           atomThs <- mapM toAtomTh atomIndicies
           childThs <- mapM toChildTh orderedChildren
           mapM (appendChild row . Just) (reverse atomThs)
           mapM (appendChild row . Just) (childThs)
           return row
    where toAtomTh i = do (Just td) <- createElement w (Just "th")
                          setInnerHTML td (Just $ show $ (pn i :: PureForm))
                          return td
          toChildTh c = do (Just td) <- createElement w (Just "th")
                           case c of
                               Left c' -> setInnerHTML td (Just [c'])
                               Right f -> setInnerHTML td (Just $ mcOf f)
                           return td
          mcOf :: (Schematizable (f (FixLang f)), CopulaSchema (FixLang f)) => FixLang f a -> String
          mcOf (h :!$: t) = mcOf h
          mcOf h = show h

--Binary propositional parsing tree. This could be written more compactly,
--but this seems conceptually clearer
data BPT = Leaf PureForm | MonNode PureForm BPT | BiNode PureForm BPT BPT

toBPT :: PureForm -> BPT
toBPT f = case children f of
              [a] -> MonNode f (toBPT a)
              [a,b] -> BiNode f (toBPT a) (toBPT b)
              _ -> Leaf f

traverseBPT :: BPT -> [Either Char PureForm]
traverseBPT (Leaf f) = [Right f]
traverseBPT (MonNode f a) = traverseBPT a ++ [Right f]
traverseBPT (BiNode f a b) = [Left '('] ++ traverseBPT a ++ [Right f] ++ traverseBPT b ++ [Left ')']
