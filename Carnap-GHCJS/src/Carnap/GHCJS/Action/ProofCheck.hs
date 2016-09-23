{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.ProofCheck (proofCheckAction) where

import Carnap.Calculi.NaturalDeduction.Checker (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, toDisplaySequence)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser (propSeqParser)
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..), parsePropProof)
import Carnap.Languages.PurePropositional.Util (toSchema)
import Carnap.GHCJS.SharedTypes
import Text.Parsec
import Data.IORef
import Data.Aeson as A
import Data.Map (empty,fromList)
import Control.Lens.Fold (toListOf)
import Lib
import GHCJS.DOM
import GHCJS.DOM.Element
--the import below is needed to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM.Types
import GHCJS.DOM.HTMLTextAreaElement (HTMLTextAreaElement, getValue, castToHTMLTextAreaElement)
import GHCJS.DOM.Document (Document,createElement, getBody, getDefaultView)
import GHCJS.DOM.Window (alert, prompt)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import Control.Monad.IO.Class (MonadIO, liftIO)

proofCheckAction :: IO ()
proofCheckAction = runWebGUI $ \w -> 
        do (Just dom) <- webViewGetDomDocument w
           (Just b) <- getBody dom
           mcheckers <- getCheckers b
           availableDerived <- newIORef []
           liftIO $ genericSendJSON RequestDerivedRulesForUser (addRules availableDerived) errcb
           case mcheckers of 
                [] -> return ()
                _ -> mapM_ (activateChecker dom availableDerived) mcheckers
    where errcb e = case fromJSON e :: Result String of
                               A.Error e -> print $ "Getting kind of meta. Error decoding error message:" ++ e
                               Success e -> print $ "Error in retrieving derived rules" ++ e

          addRules avd v = case fromJSON v :: Result [(String,DerivedRule)] of
                               A.Error e -> print $ "error decoding derived rules:" ++ e
                               Success rs -> writeIORef avd rs

getCheckers :: IsElement self => self -> IO [Maybe (Element, Element, Element, [String])]
getCheckers b =
        do ldivs <- getListOfElementsByClass b "proofchecker"
           mapM extractCheckers ldivs
        where extractCheckers Nothing = return Nothing
              extractCheckers (Just div) = 
                do mg <- getFirstElementChild div
                   cn <- getClassName div
                   -- XXX: very ugly. Clean this code
                   case mg of
                       Nothing -> return Nothing
                       Just g -> 
                         do mi <- getNextElementSibling g
                            case mi of 
                               Nothing -> return Nothing
                               (Just i) -> 
                                    do mo <- getNextElementSibling i
                                       case mo of 
                                           Nothing -> return Nothing
                                           (Just o) -> return $ Just (i,o,g,words cn)

activateChecker :: Document -> IORef [(String,DerivedRule)] -> Maybe (Element, Element, Element, [String]) -> IO ()
activateChecker _ _ Nothing  = return ()
activateChecker w drs (Just (i,o,g, classes))
        | "ruleMaker" `elem` classes = checkerWith "save rule" (trySave drs) (computeRule drs)
        | otherwise = 
            do (Just gs) <- getInnerHTML g 
               case parse seqAndLabel "" (decodeHtml gs) of
                   Left e -> setInnerHTML g (Just "Couldn't Parse Goal")
                   Right (l,s) -> do
                       setInnerHTML g (Just $ show s)
                       checkerWith "submit solution" (trySubmit l s) (checkSolution drs s) 
        where checkerWith buttonLabel buttonFunction updateres = do
                   mfeedbackDiv@(Just fd) <- createElement w (Just "div")
                   mnumberDiv@(Just nd) <-createElement w (Just "div")
                   mbt@(Just bt) <- createElement w (Just "button")
                   ref <- newIORef False
                   setAttribute fd "class" "proofFeedback"
                   setAttribute nd "class" "numbering"
                   setInnerHTML bt (Just buttonLabel)         
                   mpar@(Just par) <- getParentNode o               
                   appendChild o mnumberDiv
                   appendChild o mfeedbackDiv
                   appendChild par mbt
                   echo <- newListener $ genericUpdateResults2 (updateres w ref) g fd
                   lineupd <- newListener $ onEnter $ updateLines w nd
                   (Just w') <- getDefaultView w                    
                   buttonAct <- newListener $ buttonFunction ref w' i
                   addListener i keyUp echo False
                   addListener i keyUp lineupd False
                   addListener bt click buttonAct False                
                   setLinesTo w nd 1
                   syncScroll i o

wrap (Left (GenericError s n))  = errDiv s n Nothing
wrap (Left (NoParse e n))       = errDiv "Can't read this line. There may be a typo." n (Just $ show e)
wrap (Left (NoUnify eqs n))     = errDiv "Can't match these premises with this conclusion, using this rule" n (Just $ toUniErr eqs)
wrap (Left (NoResult n))        = "<div>&nbsp;</div>"
wrap (Right seq) = "<div>+<div><div>" ++ show seq ++ "<div></div></div>"

toUniErr eqs = "In order to apply this inference rule, there needs to be a substitution that makes at least one of these sets of pairings match:" 
                ++ (concat $ map endiv' $ map (concat . map (endiv . show) . reverse) eqs)
                -- TODO: make this less horrible, give equations internal structure so that
                -- they can be aligned properly
    where endiv e = "<div>" ++ e ++ "</div>"
          endiv' e = "<div class=\"equations\">" ++ e ++ "</div>"

checkSolution drs s w ref v (g, fd) =  do rules <- liftIO $ readIORef drs
                                          let Feedback mseq ds = toDisplaySequence (parsePropProof (fromList rules)) v
                                          ul <- genericListToUl wrap w ds
                                          setInnerHTML fd (Just "")
                                          appendChild fd (Just ul)
                                          case mseq of
                                              Nothing -> do setAttribute g "class" "goal"
                                                            writeIORef ref False
                                              (Just seq) ->  if  seq `seqSubsetUnify` s
                                                    then do setAttribute g "class" "goal success"
                                                            writeIORef ref True
                                                    else do setAttribute g "class" "goal"
                                                            writeIORef ref False
                                          return ()

computeRule drs w ref v (g, fd) = do rules <- liftIO $ readIORef drs
                                     let Feedback mseq ds = toDisplaySequence (parsePropProof (fromList rules)) v
                                     ul <- genericListToUl wrap w ds
                                     setInnerHTML fd (Just "")
                                     appendChild fd (Just ul)
                                     case mseq of
                                         Nothing -> do setInnerHTML g (Just "No Rule Found")
                                                       writeIORef ref False
                                         (Just seq) -> do setInnerHTML g (Just $ show seq)
                                                          writeIORef ref True
                                     return ()

errDiv msg lineno (Just details)= "<div>✗<div><div>Error on line " 
                                    ++ show lineno ++ ": " ++ msg 
                                    ++ "<div>see details<div>" 
                                    ++ details 
                                    ++ "</div></div></div></div></div>"
errDiv msg lineno Nothing = "<div>✗<div><div>Error on line " 
                              ++ show lineno ++ ": " ++ msg 
                              ++ "</div></div></div>"

-- XXX: this should be a library function
updateResults :: (IsElement e, IsElement e') => 
    (String -> IO e') -> e -> EventM HTMLTextAreaElement KeyboardEvent ()
updateResults f o = 
        do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
           mv <- getValue t
           case mv of 
               Nothing -> return ()
               Just v -> do liftIO $ setInnerHTML o (Just "")
                            v' <- liftIO $ f v
                            appendChild o (Just v')
                            return ()

updateResults2 :: (IsElement e, IsElement e', IsElement e'', IsElement e''') => 
    (String -> IO (e'', e''')) -> e -> e' -> EventM HTMLTextAreaElement KeyboardEvent ()
updateResults2 f o o' = genericUpdateResults2 (\v (e1, e2) -> do
    liftIO $ setInnerHTML e1 (Just "") 
    liftIO $ setInnerHTML e2 (Just "")                            
    (v',v'') <- liftIO $ f v                                      
    appendChild o (Just v')                                       
    appendChild o' (Just v'')                                     
    return ()) o o'

genericUpdateResults2 :: (IsElement e, IsElement e') => 
    (String -> (e, e') -> IO ()) -> e -> e' -> EventM HTMLTextAreaElement KeyboardEvent ()
genericUpdateResults2 f o o' = 
        do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
           mv <- getValue t
           case mv of 
               Nothing -> return ()
               Just v -> liftIO $ f v (o, o')

updateLines :: (IsElement e) => Document -> e -> EventM HTMLTextAreaElement KeyboardEvent ()
updateLines w nd = onEnter $ do (Just t) <- target :: EventM HTMLTextAreaElement KeyboardEvent (Maybe HTMLTextAreaElement)
                                mv <- getValue t
                                case mv of 
                                    Nothing -> return ()
                                    Just v -> setLinesTo w nd (1 + (length $ lines v))
                                      
setLinesTo w nd n = do setInnerHTML nd (Just "")
                       linenos <- mapM toLineNo [1 .. n]
                       mapM_ (appendChild nd . Just) linenos
    where toLineNo m = do (Just lno) <- createElement w (Just "div")
                          setInnerHTML lno (Just $ show m ++ ".")
                          return lno

trySubmit l s ref w i = do isFinished <- liftIO $ readIORef ref
                           if isFinished
                             then do (Just v) <- getValue (castToHTMLTextAreaElement i)
                                     liftIO $ sendJSON (SubmitDerivation (l ++ ":" ++ show s) v) loginCheck error
                             else alert w "not yet finished"
    where loginCheck c | c == "No User" = alert w "You need to log in before you can submit anything"
                       | c == "Clash"   = alert w "it appears you've already successfully submitted this problem"
                       | otherwise      = alert w $ "Submitted Derivation for Exercise " ++ l
          error c = alert w ("Something has gone wrong. Here's the error: " ++ c)

trySave drs ref w i = do isFinished <- liftIO $ readIORef ref
                         rules <- liftIO $ readIORef drs
                         if isFinished
                           then do (Just v) <- getValue (castToHTMLTextAreaElement i)
                                   let Feedback mseq _ = toDisplaySequence (parsePropProof (fromList rules)) v
                                   case mseq of
                                    Nothing -> alert w "A rule can't be extracted from this proof"
                                    (Just (a :|-: (SS c))) -> do
                                        let prems = map (toSchema . fromSequent) (toListOf concretes a)
                                        let conc = (toSchema . fromSequent) c
                                        mname <- prompt w "What name will you give this rule (use all capital letters!)" (Just "")
                                        case mname of
                                            (Just name) -> liftIO $ sendJSON (SaveDerivedRule name $ DerivedRule conc prems) loginCheck error
                                            Nothing -> alert w "No name entered"
                           else alert w "not yet finished"
    where loginCheck c | c == "No User" = alert w "You need to log in before you can save a rule"
                       | c == "Clash"   = alert w "it appears you've already got a rule with this name"
                       | otherwise      = alert w $ "Saved your new rule!"
          error c = alert w ("Something has gone wrong. Here's the error: " ++ c)

seqAndLabel =  do label <- many (digit <|> char '.')
                  spaces
                  s <- propSeqParser
                  return (label,s)
