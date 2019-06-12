{-#LANGUAGE FlexibleContexts, RankNTypes #-}
module Carnap.GHCJS.Action.CounterModel (counterModelAction) where

import Lib
import Carnap.GHCJS.SharedTypes
import Carnap.Core.Data.Types (Form(..), Term(..), Arity(..), Fix(..), arityInt)
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Util
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Logic 
import Carnap.Languages.PureFirstOrder.Semantics
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Util (universalClosure)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.Event (initEvent)
import GHCJS.DOM.EventTarget (dispatchEvent)
import GHCJS.DOM.Document (createElement, createEvent, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.EventM (newListener, addListener, EventM, target)
import GHCJS.DOM.HTMLInputElement (HTMLInputElement, getValue, setValue)
import qualified GHCJS.DOM.HTMLSelectElement as S (getValue, setValue) 
import Text.Parsec
import Data.Typeable (Typeable)
import Data.List (nub)
import Data.Maybe (catMaybes)
import Data.Either (isLeft)
import Data.Map as M (Map, lookup, foldr, insert, fromList, toList)
import Data.IORef (newIORef, IORef, readIORef,writeIORef, modifyIORef)
import Data.List (intercalate)
import Data.Text (pack)
import Control.Monad (filterM)
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
            Just "constraint" -> checkerWith (formListPairParser <* eof) createConstrainedCounterModeler
            Just "validity" -> checkerWith (seqParser <* eof) createValidityCounterModeler
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
                          ref <- newIORef $ Left "Please press submit to check your answer"
                          bw <- buttonWrapper w
                          check <- cmbuilder w f (i,o) bw opts
                          fields <- catMaybes <$> getListOfElementsByTag o "label"
                          mapM (setField w fields) (makeGivens opts)
                          case M.lookup "submission" opts of
                              Just s | take 7 s == "saveAs:" -> do
                                  let l = Prelude.drop 7 s
                                  bt1 <- doneButton w "Submit"
                                  appendChild bw (Just bt1)
                                  submit <- newListener $ submitCounterModel opts ref check fields (show f) l
                                  addListener bt1 click submit False                
                              _ -> return ()
                          if "nocheck" `inOpts` opts then return () 
                          else do
                              bt2 <- questionButton w "Check"
                              appendChild bw (Just bt2)
                              checkIt <- newListener $ checkCounterModeler ref fields check
                              addListener bt2 click checkIt False                
                          Just par <- getParentNode o
                          appendChild par (Just bw)
                          return ()
                _ -> print "countermodeler lacks a goal"

          checkCounterModeler ref fields check = do correct <- liftIO check
                                                    validated <- liftIO $ validateModel fields
                                                    case (correct, validated) of 
                                                       (Left err,_) -> do
                                                           liftIO $ writeIORef ref (Left err)
                                                           message err
                                                           setAttribute i "class" "input incompleteCM"
                                                       (_,Left err) -> do
                                                           liftIO $ writeIORef ref (Left err)
                                                           message err
                                                           setAttribute i "class" "input incompleteCM"
                                                       _ -> do
                                                           liftIO $ writeIORef ref correct
                                                           message "Success!"
                                                           setAttribute i "class" "input completeCM"

submitCounterModel:: Map String String -> IORef (Either String ())->  IO (Either String ())-> [Element] -> String -> String -> EventM HTMLInputElement e ()
submitCounterModel opts ref check fields s l = do isDone <- liftIO $ readIORef ref
                                                  case isDone of
                                                      Right _ -> trySubmit CounterModel opts l (ProblemContent (pack s)) True
                                                      Left err | not ("exam" `inOpts` opts) -> message err
                                                      _ -> do correct <- liftIO check
                                                              validated <- liftIO $ validateModel fields
                                                              case (correct, validated) of
                                                                 (Right _, Right _) -> trySubmit CounterModel opts l (ProblemContent (pack s)) True
                                                                 _ -> do extracted <- liftIO $ mapM extractField fields
                                                                         trySubmit CounterModel opts l (CounterModelDataOpts (pack s) extracted (M.toList opts)) False


createSimpleCounterModeler :: Document -> [PureFOLForm] -> (Element,Element)
    -> Element -> Map String String 
    -> IO (IO (Either String ()))
createSimpleCounterModeler w fs (i,o) bw opts = 
        do setInnerHTML i (Just . intercalate ", " . map (rewriteWith opts . show) $ fs)
           theModel <- initModel
           prepareModelUI w fs (i,o) theModel bw opts
           return (formsInModel theModel)
    where formsInModel mdl = do
              m <- readIORef mdl
              let tvs = map (unform . satisfies m . universalClosure) fs
              if and tvs then return $ Right ()
              else do 
                 let falses = intercalate ", " $ map (show . snd) . filter (not . fst) $ (zip tvs fs)
                 return $ Left $ "Not all formulas are true in this model. Take another look at: " ++  falses ++ "."

createConstrainedCounterModeler :: Document -> ([PureFOLForm],[PureFOLForm]) -> (Element,Element)
    -> Element -> Map String String 
    -> IO (IO (Either String ()))
createConstrainedCounterModeler w (cs,fs) (i,o) bw opts = 
        do setInnerHTML i (Just . intercalate ", " . map (rewriteWith opts . show) $ fs)
           theModel <- initModel
           prepareModelUI w (cs ++ fs) (i,o) theModel bw opts
           return (formsInModel theModel)
    where formsInModel mdl = do
              m <- readIORef mdl
              let tvs = map (unform . satisfies m . universalClosure) fs
              let ctvs = map (unform . satisfies m . universalClosure) cs
              if not (and tvs) then do 
                 let falses = intercalate ", " $ map (show . snd) . filter (not . fst) $ (zip tvs fs)
                 return $ Left $ "Not all formulas are true in this model. Take another look at: " ++  falses ++ "."
              else if not (and ctvs) then return $ Left "Not all the constraints for this problem are satisfied by this model."
              else return $ Right ()

createValidityCounterModeler :: Document -> ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)) -> (Element,Element) 
    -> Element -> Map String String 
    -> IO (IO (Either String ()))
createValidityCounterModeler w seq@(antced :|-: succed) (i,o) bw opts = 
        do setInnerHTML i (Just . show $ seq)
           theModel <- initModel
           prepareModelUI w fs (i,o) theModel bw opts
           return (formsInModel theModel)
    where ants = map fromSequent $ toListOf concretes antced
          sucs = map fromSequent $ toListOf concretes succed
          fs = ants ++ sucs
          formsInModel mdl = do
              m <- readIORef mdl
              let ptvs = map (unform . satisfies m . universalClosure) ants
                  ctvs = map (unform . satisfies m . universalClosure) sucs
              if not (and ptvs) then do 
                 let falses = intercalate ", " $ map (show . snd) . filter (not . fst) $ (zip ptvs ants)
                 return $ Left $ "not all premises are true in this model. Take another look at: " ++ falses ++ "."
              else if or ctvs then do 
                 let trues = intercalate ", " $ map (show . snd) . filter fst $ (zip ptvs ants)
                 return $ Left $ "not all conclusions are false in this model. Take another look at: " ++ trues ++ "."
              else return $ Right ()

prepareModelUI :: Document -> [PureFOLForm] -> (Element,Element) -> IORef PolyadicModel
    -> Element -> Map String String 
    -> IO ()
prepareModelUI w fs (i,o) mdl bw opts = do
           Just domainLabel <- createElement w (Just "label")
           setInnerHTML domainLabel (Just "Domain: ")
           (domainInput,domainWarn) <- parsingInput w things domainUpdater
           setAttribute domainInput "name" "Domain"
           setValue (castToHTMLInputElement domainInput) (Just "0")
           mapM (appendChild domainLabel . Just) [domainInput, domainWarn]
           appendChild o (Just domainLabel)
           appendRelationInputs w o fs mdl
           appendPropInputs w o fs mdl
           let ts = concatMap (toListOf termsOf) fs
           appendConstantInputs w o ts mdl
    where domainUpdater ts = liftIO $ modifyIORef mdl (\m -> m { monadicPart = (monadicPart m) {domain = ts}})
          things = parseInt `sepEndBy1` (spaces *> char ',' <* spaces)

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

appendPropInputs :: Document -> Element -> [PureFOLForm] -> IORef PolyadicModel -> IO ()
appendPropInputs w o fs mdl = do let sfs = nub . concatMap (toListOf cosmos) $ fs
                                 mapM_ appendPropInput sfs
    where appendPropInput t = do minput <- getPropInput w t mdl
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
                                 setAttribute constInput "name" (show t)
                                 setValue (castToHTMLInputElement constInput) (Just "0")
                                 appendChild constLabel (Just constInput)
                                 appendChild constLabel (Just parseWarn)
                                 return $ Just constLabel
    where constUpdater ext = case addConstant t mdl ext of
                                 Just io -> liftIO io
                                 Nothing -> return ()

getPropInput :: Document -> PureFOLForm -> IORef PolyadicModel -> IO (Maybe Element)
getPropInput w f mdl = case addProposition f mdl False of
                            Nothing -> return Nothing
                            Just _ -> do
                                 Just propLabel <- createElement w (Just "label")
                                 setInnerHTML propLabel (Just $ show f ++ ": ")
                                 [Just propSelect, Just pt ,Just pf] <- mapM (createElement w . Just) ["select","option","option"]
                                 setInnerHTML pt (Just "True")
                                 setInnerHTML pf (Just "False")
                                 setAttribute pf "selected" "selected"
                                 mapM (appendChild propSelect) [Just pt,Just pf]
                                 setAttribute propSelect "name" (show f)
                                 whenChange <- newListener propUpdater
                                 whenInit <- newListener propUpdater
                                 addListener propSelect initialize whenInit False
                                 addListener propSelect change whenChange False
                                 appendChild propLabel (Just propSelect)
                                 return $ Just propLabel
    where propUpdater :: EventM HTMLInputElement Event ()
          propUpdater = do 
             Just t <- target
             sval <- getValue t 
             case addProposition f mdl (if sval == Just "True" then True else False) of 
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
                                         setAttribute relationInput "name" (show (blankTerms f))
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
                                    
addProposition :: PureFOLForm -> IORef PolyadicModel -> Bool -> Maybe (IO ())
addProposition t mdl extension = case preview _propIndex t of
                                  Nothing -> Nothing
                                  Just idx -> Just $ modifyIORef mdl $ \m -> m
                                        { monadicPart = (monadicPart m) 
                                            { proposition = \n -> if n == idx then Form extension else proposition (monadicPart m) n }
                                        }

initModel :: IO (IORef PolyadicModel)
initModel = newIORef (PolyadicModel 
                     { relation = \a _ -> toRelation mempty a
                     , function = \a _ -> toFunction mempty a
                     , monadicPart = MonadicModel
                        { domain = [Term 0]
                        , property = \_ _ -> Form False
                        , name = \_ -> Term 0
                        , proposition = \_ -> Form False
                        }
                     })

parsingInput :: Document -> Parsec String () a -> (forall e. IsEvent e => a -> EventM HTMLInputElement e ()) -> IO (Element,Element)
parsingInput w parser event = do Just theInput <- createElement w (Just "input")
                                 Just theWarning <- createElement w (Just "span")
                                 whenKey <- newListener (doesParse theWarning)
                                 whenInit <- newListener (doesParse theWarning)
                                 addListener theInput initialize whenInit False
                                 addListener theInput keyUp whenKey False
                                 return (theInput,theWarning)
    where doesParse :: IsEvent e => Element -> EventM HTMLInputElement e ()
          doesParse warn = do 
             Just t <- target 
             Just ival <- getValue t
             case parse (parser <* eof) "" ival of
                 Left e -> liftIO $ setInnerHTML warn (Just "⚠") --XXX: Consider a tooltip here.
                 Right x -> (liftIO $ setInnerHTML warn (Just "")) >> event x

extractField :: Element -> IO (String, String)
extractField field = do inputs <- getListOfElementsByTag field "input"
                        selects <- getListOfElementsByTag field "select"
                        case (inputs,selects) of
                            ([Just input],_) -> do 
                              Just fieldName <- getAttribute input "name"
                              Just ival <- getValue (castToHTMLInputElement input)
                              return (fieldName, ival) 
                            (_,[Just select]) -> do 
                              Just fieldName <- getAttribute select "name"
                              Just sval <- S.getValue (castToHTMLSelectElement select)
                              return (fieldName, sval)

parseInt :: Parsec String () Thing
parseInt = Term . read <$> many1 digit

makeGivens :: Map String String -> [(String,String)]
makeGivens opts = case M.lookup "content" opts of
                      Nothing -> []
                      Just t -> map (clean . break (== ':')) . lines $ t
    where clean (x,y) = (x, tail y)

--XXX: a lot of unsafe pattern matching and catMaybe here...
validateModel :: [Element] -> IO (Either String ())
validateModel fields = do inputs <- concat <$> mapM (\f -> getListOfElementsByTag f "input") fields
                          names <- mapM (\(Just i) -> getAttribute i "name") inputs
                          let [Just domain] = map fst . filter (\f -> snd f == Just "Domain") $ zip inputs names
                          Just domainString <- getValue (castToHTMLInputElement domain)
                          case parse (parseInt `sepEndBy1` (spaces *> char ',' <* spaces)) "" domainString of
                              Left e -> return $ Left $ "Couldn't read domain specification: " ++ show e
                              Right things -> do
                                  if null things 
                                      then return $ Left "The domain cannot be empty"
                                      else do
                                          otherStrings <- mapM (getValue . castToHTMLInputElement) (catMaybes inputs)
                                          let otherContents = zip (map (parse extractor "" . clean) (catMaybes otherStrings)) names
                                          case filter (isLeft . fst) otherContents of
                                              (Left err,Just n):_ -> return $ Left $ "Couldn't read specification for " ++ n ++ ": " ++ show err
                                              [] -> case filter (\(Right ext,_) -> not (ext `subset` things)) otherContents of
                                                   (_,Just n):_ -> return $ Left $ "The extension of " ++ n ++ " is not contained in the domain."
                                                   [] -> return $ Right ()
                       
    where clean (',':xs) = ' ':clean xs
          clean ('[':xs) = ' ':clean xs
          clean (']':xs) = ' ':clean xs
          clean (y:ys) = y:clean ys
          clean [] = []
          extractor = spaces *> (parseInt `sepEndBy` spaces) <* spaces
          subset (x:xs) y = x `elem` y && xs `subset` y
          subset [] y = True


setField :: Document -> [Element] -> (String,String) -> IO ()
setField w fields (name,val) = do inputs <- concat <$> mapM (\f -> getListOfElementsByTag f "input") fields
                                  selects <- concat <$> mapM (\f -> getListOfElementsByTag f "select") fields
                                  names <- mapM (\(Just i) -> getAttribute i "name") (inputs ++ selects)
                                  let fs = map fst . filter (\f -> snd f == Just name) $ zip (inputs ++ selects) names
                                  case fs of
                                   [Just f] -> do tn <- getTagName f
                                                  case tn of 
                                                    Just "INPUT" -> setValue (castToHTMLInputElement f) (Just val)
                                                    Just "SELECT" -> S.setValue (castToHTMLSelectElement f) (Just val)
                                                    Just s -> print $ "unrecognized tag:" ++ s
                                                    Nothing -> print "no tagname"
                                                  Just init <- createEvent w "Event"
                                                  initEvent init "initialize" True True
                                                  dispatchEvent f (Just init)
                                                  return ()
                                   _ -> print $ "missing or duplicated field " ++ name ++ "in countermodel spec"
