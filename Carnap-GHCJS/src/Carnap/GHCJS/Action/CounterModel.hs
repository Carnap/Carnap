{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.CounterModel (counterModelAction) where

import Lib
import Carnap.Core.Data.Types (Form(..), Term(..), Arity(..), Fix(..), arityInt)
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Util
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Logic 
import Carnap.Languages.PureFirstOrder.Semantics
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Util (universalClosure)
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.Document (createElement, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.EventM (newListener, addListener, EventM, target)
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, getValue, setValue)
import Text.Parsec
import Data.Typeable (Typeable)
import Data.List (nub)
import Data.Map as M (Map, lookup, foldr, insert, fromList, toList)
import Data.IORef (newIORef, IORef, readIORef,writeIORef, modifyIORef)
import Data.List (intercalate)
import Control.Monad.IO.Class (liftIO)
import Control.Lens

counterModelAction :: IO ()
counterModelAction = initElements getCounterModelers activateCounterModeler

getCounterModelers :: Document -> HTMLElement -> IO [Maybe (Element, Element, Map String String)]
getCounterModelers d = genInOutElts d "div" "div" "countermodeler"

activateCounterModeler :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateCounterModeler w (Just (i,o,opts)) = do
        case M.lookup "countermodelertype" opts of
            Just "simple" -> checkerWith (formListParser <* eof) createSimpleCounterModeler
            Just "validity" -> checkerWith seqParser createValidityCounterModeler
            _  -> return ()
    where (formParser,seqParser) = case M.lookup "system" opts >>= \sys -> (,) <$> ndParseForm `ofFOLSys` sys <*> ndParseSeq `ofFOLSys` sys of
                                         Just pair -> pair
                                         Nothing -> let Just fp = ndParseForm `ofFOLSys` "firstOrder"
                                                        Just sp = ndParseSeq `ofFOLSys` "firstOrder"
                                                        in (fp,sp)
          formListParser = formParser `sepEndBy1` (spaces *> char ',' <* spaces)
          formListPairParser = do gs <- try (formListParser <* char ':') <|> return []
                                  optional (char ':')
                                  spaces
                                  fs <- formListParser
                                  return (gs,fs)
          
          checkerWith parser cmbuilder = 
            case M.lookup "goal" opts of
                Just g ->
                  case parse parser "" g of
                      Left e -> setInnerHTML o (Just $ show e) 
                      Right f -> do
                          ref <- newIORef False
                          bw <- buttonWrapper w
                          check <- cmbuilder w f (i,o) ref bw opts
                          if "nocheck" `inOpts` opts then return () 
                          else do
                              bt2 <- questionButton w "Check"
                              appendChild bw (Just bt2)
                              checkIt <- newListener $ checkCounterModeler ref check
                              addListener bt2 click checkIt False                
                          Just par <- getParentNode o
                          appendChild par (Just bw)
                          return ()
                _ -> print "countermodeler lacks a goal"

          checkCounterModeler ref check = do correct <- liftIO $ check
                                             if correct 
                                                 then do message "Success!"
                                                         liftIO $ writeIORef ref True
                                                         setAttribute i "class" "input completeCM"
                                                 else do message "Something's not quite right"
                                                         liftIO $ writeIORef ref False
                                                         setAttribute i "class" "input incompleteCM"

createSimpleCounterModeler :: Document -> [PureFOLForm] -> (Element,Element) -> IORef Bool 
    -> Element -> Map String String 
    -> IO (IO Bool)
createSimpleCounterModeler w fs (i,o) ref bw opts = 
        do setInnerHTML i (Just . intercalate ", " . map (rewriteWith opts . show) $ fs)
           theModel <- initModel
           Just domainLabel <- createElement w (Just "label")
           setInnerHTML domainLabel (Just "Domain: ")
           (domainInput,domainWarn) <- parsingInput w things (domainUpdater theModel)
           mapM (appendChild domainLabel . Just) [domainInput, domainWarn]
           appendChild o (Just domainLabel)
           appendRelationInputs w o fs theModel
           let ts = concatMap (toListOf termsOf) fs
           appendConstantInputs w o ts theModel
           return (formsInModel theModel)
    where things = parseInt `sepEndBy1` (spaces *> char ',' <* spaces)
          domainUpdater mdl ts = liftIO $ modifyIORef mdl (\m -> m { monadicPart = (monadicPart m) {domain = ts}})
          formsInModel mdl = do
              m <- readIORef mdl
              return $ all (unform . satisfies m) (map universalClosure fs)

createValidityCounterModeler = undefined

appendRelationInputs :: Document -> Element -> [PureFOLForm] -> IORef PolyadicModel -> IO ()
appendRelationInputs w o fs mdl = do let sfs = nub . concatMap (toListOf cosmos) $ fs
                                     mapM_ appendRelationInput sfs
    where appendRelationInput f = do minput <- getRelationInput w f mdl
                                     case minput of 
                                        Nothing -> return Nothing
                                        Just input -> appendChild o (Just input)

appendConstantInputs :: Document -> Element -> [PureFOLTerm] -> IORef PolyadicModel -> IO ()
appendConstantInputs w o ts mdl = do let sts = nub . concatMap (toListOf cosmos) $ ts
                                     mapM_ appendConstantInput sts
    where appendConstantInput t = do minput <- getConstInput w t mdl
                                     case minput of 
                                        Nothing -> return Nothing
                                        Just input -> appendChild o (Just input)

getConstInput :: Document -> PureFOLTerm -> IORef PolyadicModel -> IO (Maybe Element)
getConstInput w t mdl = case addConstant t mdl (Term 0) of
                            Nothing -> return Nothing
                            Just _ -> do
                                 Just constLabel <- createElement w (Just "label")
                                 setInnerHTML constLabel (Just $ show t ++ ": ")
                                 (constInput,parseWarn) <- parsingInput w parseInt constUpdater
                                 appendChild constLabel (Just constInput)
                                 appendChild constLabel (Just parseWarn)
                                 return $ Just constLabel
    where constUpdater ext = case addConstant t mdl ext of
                                 Just io -> liftIO io
                                 Nothing -> return ()


getRelationInput :: Document -> PureFOLForm -> IORef PolyadicModel -> IO (Maybe Element)
getRelationInput w f mdl = case addRelation f mdl [] of
                             Nothing -> return Nothing
                             Just io -> do 
                                 mlen <- io
                                 case mlen of 
                                      Nothing -> return Nothing
                                      Just n -> do
                                         Just relationLabel <- createElement w (Just "label")
                                         setInnerHTML relationLabel (Just $ show (blankTerms f) ++ ": ")
                                         (relationInput,parseWarn) <- parsingInput w (ntuples n) relationUpdater
                                         appendChild relationLabel (Just relationInput)
                                         appendChild relationLabel (Just parseWarn)
                                         return $ Just relationLabel
    where tuple = char '[' *> (parseInt `sepEndBy` (spaces *> char ',' <* spaces)) <* char ']'
          ntuple n = do t <- tuple; if length t == n then return t else fail ("This extension should be made only of " ++ show n ++ "-tuples")
          ntuples n = ntuple n `sepEndBy` (spaces *> char ',' <* spaces)
          relationUpdater ext = case addRelation f mdl ext of
                                     Just io -> liftIO io >> return ()
                                     Nothing -> return ()

blankTerms :: PureFOLForm -> PureFOLForm
blankTerms f = set termsOf (foVar "_") f

addRelation :: PureFOLForm -> IORef PolyadicModel -> [[Thing]] -> Maybe (IO (Maybe Int))
addRelation f mdl extension = withArity onRel (AZero :: Arity (Term Int) (Form Bool) (Form Bool)) f
    where _predIdx' :: Typeable ret =>  Prism' (PureLanguageFOL ret) (Int, Arity (Term Int) (Form Bool) ret)
          _predIdx' = _predIdx
          onRel :: Arity (Term Int) (Form Bool) ret -> PureLanguageFOL ret -> IO (Maybe Int)
          onRel _ f@(Fx _) = case preview _predIdx' f of 
                 Nothing -> return Nothing
                 Just (idx,a) -> do
                     modifyIORef mdl $ \m -> m
                        { relation = \a' n -> if n == idx && show a == show a'
                            then toRelation extension a'
                            else relation m a' n
                        }
                     return $ Just (arityInt a)

addConstant :: PureFOLTerm-> IORef PolyadicModel -> Thing -> Maybe (IO ())
addConstant t mdl extension = case preview _constIdx t of
                                  Nothing -> Nothing
                                  Just idx -> Just $ modifyIORef mdl $ \m -> m
                                        { monadicPart = (monadicPart m) 
                                            { name = \n -> if n == idx then extension else name (monadicPart m) n }
                                        }
                                    

initModel :: IO (IORef PolyadicModel)
initModel = newIORef (PolyadicModel 
                     { relation = \a _ -> toRelation mempty a
                     , function = \a _ -> toFunction mempty a
                     , monadicPart = MonadicModel
                        { domain = []
                        , property = \_ _ -> Form False
                        , name = \_ -> Term 0
                        , proposition = \_ -> Form False
                        }
                     })

parsingInput :: Document -> Parsec String () a -> (a -> EventM HTMLInputElement KeyboardEvent ()) -> IO (Element,Element)
parsingInput w parser event = do Just theInput <- createElement w (Just "input")
                                 Just theWarning <- createElement w (Just "span")
                                 whenParse <- newListener (doesParse theWarning)
                                 addListener theInput keyUp whenParse False
                                 return (theInput,theWarning)
    where doesParse warn = do 
             Just t <- target :: EventM HTMLInputElement KeyboardEvent (Maybe HTMLInputElement)
             Just ival <- getValue t :: EventM HTMLInputElement KeyboardEvent (Maybe String)
             case parse (parser <* eof) "" ival of
                 Left e -> liftIO $ setInnerHTML warn (Just "⚠") --XXX: Consider a tooltip here.
                 Right x -> (liftIO $ setInnerHTML warn (Just "")) >> event x

parseInt :: Parsec String () Thing
parseInt = Term . read <$> many1 digit
