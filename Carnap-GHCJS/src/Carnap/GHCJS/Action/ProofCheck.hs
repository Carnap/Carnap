{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.ProofCheck (proofCheckAction) where

import Carnap.Calculi.NaturalDeduction.Checker (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, processLine, processLineFitch, hoProcessLine, toDisplaySequence)
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftLang)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Logic as P (DerivedRule(..), parsePropProof,parseFitchPropProof, propSeqParser) 
import Carnap.Languages.PureFirstOrder.Logic as FOL (DerivedRule(..), parseFOLProof, folSeqParser) 
import Carnap.Languages.PureSecondOrder.Logic (parseMSOLProof, msolSeqParser) 
import Carnap.Languages.PurePropositional.Util (toSchema)
import Carnap.GHCJS.SharedTypes
import Text.Parsec (parse)
import Data.IORef (IORef, newIORef,writeIORef,readIORef)
import Data.Aeson as A
import qualified Data.Map as M (fromList,map) 
import Control.Lens.Fold (toListOf)
import Lib
import Carnap.GHCJS.Widget.ProofCheckBox (checkerWith, CheckerOptions(..),Button(..))
import Carnap.GHCJS.Widget.RenderDeduction (renderDeduction)
import GHCJS.DOM.Element (setInnerHTML,getInnerHTML, setAttribute)
import GHCJS.DOM.HTMLElement (insertAdjacentElement)
--the import below is needed to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM.Types
import GHCJS.DOM.HTMLTextAreaElement (getValue)
import GHCJS.DOM.Document (createElement, getDefaultView)
import GHCJS.DOM.Window (prompt)
import GHCJS.DOM.Node (appendChild, getParentNode )
--import GHCJS.DOM.EventM
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (modify,get,execState)
import Control.Concurrent

proofCheckAction :: IO ()
proofCheckAction = do availableDerived <- newIORef []
                      print "starting"
                      genericSendJSON RequestDerivedRulesForUser (addRules availableDerived) errcb
                      initElements getCheckers (activateChecker availableDerived)

errcb :: Value -> IO ()
errcb e = case fromJSON e :: Result String of
               A.Error e' -> print $ "Getting kind of meta. Error decoding error message: " ++ e'
               Success e' -> print $ "Error in retrieving derived rules: " ++ e'

--- XXX bizarre error arises when I try to send the JSON for the derived
--- rules directly. It worked on previous versions of ghcjs, so I'm going
--- to wait until I move all this to GHC 8.2 and the latest ghcjs before
--- spending too much time trying to fix.
--
--  Notes: the bug arises only with the custom toJSON instance for
--  DerivedRule. toJSON and fromJSON seem to work fine for that instance.
addRules :: IORef [(String, P.DerivedRule)] -> Value -> IO ()
addRules avd v =  case fromJSON v :: Result String of
                    A.Error e -> do print $ "error decoding derived rules: " ++ e
                                    print $ "recieved string: " ++ show v
                    Success s -> do let v' = read s :: Value
                                    case fromJSON v' :: Result [(String,P.DerivedRule)] of
                                          A.Error e -> do print $ "error decoding derived rules: " ++ e
                                                          print $ "recieved JSON: " ++ show v
                                          Success rs -> do print $ show rs
                                                           writeIORef avd rs

getCheckers :: IsElement self => self -> IO [Maybe IOGoal]
getCheckers = getInOutGoalElts "proofchecker"

activateChecker ::  IORef [(String,P.DerivedRule)] -> Document -> Maybe IOGoal -> IO ()
activateChecker _ _ Nothing  = return ()
activateChecker drs w (Just iog@(IOGoal i o g classes))
        | "ruleMaker" `elem` classes = 
            checkerWith CheckerOptions {submit = Just Button 
                                            { label = "save rule"
                                            , action = trySave drs
                                            }
                                        } (computeRule drs) iog w
        | "playground" `elem` classes = do pd <- makeDisplay
                                           checkerWith CheckerOptions {submit = Nothing } 
                                                (fitchPlayground drs pd) iog w
        | "firstOrder" `elem` classes = 
                        tryParse buildOptions folSeqParser 
                            (\s mtref pd -> folCheckSolution drs s mtref)
        | "secondOrder" `elem` classes = 
                        tryParse buildOptions msolSeqParser
                            (\s mtref pd -> msolCheckSolution s mtref)
        | "LogicBook" `elem` classes = 
                        tryParse buildOptions propSeqParser
                            (\s mtref pd -> checkSolutionFitch drs s pd) 
        | otherwise = tryParse buildOptions propSeqParser
                            (\s mtref pd -> checkSolution drs s) 
        where tryParse options seqParse checker = do
                  (Just gs) <- getInnerHTML g 
                  case parse (withLabel seqParse) "" (decodeHtml gs) of
                       Left e -> setInnerHTML g (Just "Couldn't Parse Goal")
                       Right (l,s) -> do setInnerHTML g (Just $ show s)
                                         mtref <- newIORef Nothing
                                         pd <- makeDisplay
                                         case submit options of
                                             Nothing -> checkerWith options
                                                         (checker s mtref pd)
                                                         iog w
                                             Just b -> checkerWith 
                                                         options {submit = Just b {action = trySubmit l s }}
                                                         (checker s mtref pd)
                                                         iog w
              makeDisplay = do (Just pd) <- createElement w (Just "div")
                               setAttribute pd "class" "proofDisplay"
                               (Just parent) <- getParentNode o
                               insertAdjacentElement (castToHTMLElement parent) "afterend" (Just pd)
                               return pd

              standardOptions = 
                    CheckerOptions {
                         submit = Just Button { label = "Submit Solution"
                                              , action = \r w e -> return ()
                                              }
                                   }
              buildOptions = execState (do if "Demo" `elem` classes 
                                                   then modify (\o -> o {submit = Nothing})
                                                   else return ())
                                            standardOptions

checkSolution drs s w ref v (g, fd)   =  do rules <- liftIO $ readIORef drs 
                                            -- XXX this is here, rather than earlier, 
                                            -- because if this ref is read too quickly, the async callback for the rules fails. 
                                            let Feedback mseq ds = toDisplaySequence processLine . parsePropProof (M.fromList rules) $ v
                                            updateGoal s w ref (g, fd) mseq ds

checkSolutionFitch drs s pd w ref v (g, fd) =  do rules <- liftIO $ readIORef drs 
                                                  let ded = parseFitchPropProof (M.fromList rules) v
                                                  renderedProof <- renderDeduction w ded
                                                  setInnerHTML pd (Just "")
                                                  appendChild pd (Just renderedProof)
                                                  let Feedback mseq ds = toDisplaySequence processLineFitch ded
                                                  updateGoal s w ref (g, fd) mseq ds

folCheckSolution drs s mtref w ref v (g, fd) = 
        do mt <- readIORef mtref
           rules <- liftIO $ readIORef drs 
           case mt of
               Just t -> killThread t
               Nothing -> return ()
           t' <- forkIO $ do threadDelay 200000
                             let Feedback mseq ds = toDisplaySequence hoProcessLine . parseFOLProof (M.map liftDerivedRule $ M.fromList rules) $ v
                             updateGoal s w ref (g, fd) mseq ds
           writeIORef mtref (Just t')
           return ()

msolCheckSolution s mtref w ref v (g, fd) = 
        do mt <- readIORef mtref
           case mt of
               Just t -> killThread t
               Nothing -> return ()
           t' <- forkIO $ do threadDelay 200000
                             let Feedback mseq ds = toDisplaySequence hoProcessLine . parseMSOLProof $ v
                             updateGoal s w ref (g, fd) mseq ds
           writeIORef mtref (Just t')
           return ()

updateGoal s w ref (g, fd) mseq ds = do ul <- genericListToUl wrap w ds
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
                                     let Feedback mseq ds = toDisplaySequence processLine . parsePropProof (M.fromList rules) $ v
                                     ul <- genericListToUl wrap w ds
                                     setInnerHTML fd (Just "")
                                     appendChild fd (Just ul)
                                     case mseq of
                                         Nothing -> do setInnerHTML g (Just "No Rule Found")
                                                       writeIORef ref False
                                         (Just seq) -> do setInnerHTML g (Just $ show seq)
                                                          writeIORef ref True
                                     return ()

fitchPlayground drs pd w ref v (g, fd) =  do rules <- liftIO $ readIORef drs 
                                             let ded = parseFitchPropProof (M.fromList rules) v
                                             renderedProof <- renderDeduction w ded
                                             setInnerHTML pd (Just "")
                                             appendChild pd (Just renderedProof)
                                             let Feedback mseq ds = toDisplaySequence processLineFitch ded
                                             ul <- genericListToUl wrap w ds
                                             setInnerHTML fd (Just "")
                                             appendChild fd (Just ul)
                                             case mseq of
                                                 Nothing -> do setInnerHTML g (Just "Nothing Proven")
                                                               writeIORef ref False
                                                 (Just seq) -> do setInnerHTML g (Just $ show seq)
                                                                  writeIORef ref True
                                             return ()

                                               

trySubmit l s ref w i = do isFinished <- liftIO $ readIORef ref
                           if isFinished
                             then do (Just v) <- getValue (castToHTMLTextAreaElement i)
                                     msource <- liftIO submissionSource
                                     key <- liftIO assignmentKey
                                     case msource of 
                                        Nothing -> message "Not able to identify problem source"
                                        Just source -> liftIO $ sendJSON 
                                                        (SubmitDerivation (l ++ ":" ++ show s) v source key) 
                                                        (loginCheck $ "Submitted Derivation for Exercise " ++ l)
                                                        errorPopup
                             else message "not yet finished"

trySave drs ref w i = do isFinished <- liftIO $ readIORef ref
                         rules <- liftIO $ readIORef drs
                         if isFinished
                           then do (Just v) <- getValue (castToHTMLTextAreaElement i)
                                   let Feedback mseq _ = toDisplaySequence processLine . parsePropProof (M.fromList rules) $ v
                                   case mseq of
                                    Nothing -> message "A rule can't be extracted from this proof"
                                    (Just (a :|-: (SS c))) -> do
                                        -- XXX : throw a more transparent error here if necessary
                                        let prems = map (toSchema . fromSequent) (toListOf concretes a)
                                        let conc = (toSchema . fromSequent) c
                                        mname <- prompt w "What name will you give this rule (use all capital letters!)" (Just "")
                                        case mname of
                                            (Just name) -> if allcaps name 
                                                               then liftIO $ sendJSON (SaveDerivedRule name $ P.DerivedRule conc prems) loginCheck error
                                                               else message "rule name must be all capital letters"
                                            Nothing -> message "No name entered"
                           else message "not yet finished"
    where loginCheck c | c == "No User" = message "You need to log in before you can save a rule"
                       | c == "Clash"   = message "it appears you've already got a rule with this name"
                       | otherwise      = message "Saved your new rule!" >> reloadPage
          error c = message ("Something has gone wrong. Here's the error: " ++ c)
          allcaps s = and (map (`elem` "ABCDEFGHIJKLMNOPQRSTUVWXYZ") s)

-------------------------
--  Utility Functions  --
-------------------------

wrap (Left (GenericError s n))  = errDiv "?" s n Nothing
wrap (Left (NoParse e n))       = errDiv "⚠" "Can't read this line. There may be a typo." n (Just $ show e)
wrap (Left (NoUnify eqs n))     = errDiv "✗" "Can't match these premises with this conclusion, using this rule" n (Just $ toUniErr eqs)
wrap (Left (NoResult _))        = "<div>&nbsp;</div>"
wrap (Right s)                  = "<div>+<div><div>" ++ show s ++ "<div></div></div>"

toUniErr eqs = "In order to apply this inference rule, there needs to be a substitution that makes at least one of these sets of pairings match:" 
                ++ (concat $ map endiv' $ map (concat . map (endiv . show) . reverse) eqs)
                -- TODO make this less horrible, give equations internal
                -- structure so that they can be aligned properly
    where endiv e = "<div>" ++ e ++ "</div>"
          endiv' e = "<div class=\"equations\">" ++ e ++ "</div>"

liftDerivedRule (P.DerivedRule conc prems) = FOL.DerivedRule (liftLang conc) (map liftLang prems)

errDiv :: [Char] -> [Char] -> Int -> Maybe [Char] -> [Char]
errDiv ico msg lineno (Just details) = "<div>" ++ ico ++ "<div><div>Error on line " 
                                       ++ show lineno ++ ": " ++ msg 
                                       ++ "<div>see details<div>" 
                                       ++ details 
                                       ++ "</div></div></div></div></div>"
errDiv ico msg lineno Nothing = "<div>" ++ ico ++ "<div><div>Error on line " 
                              ++ show lineno ++ ": " ++ msg 
                              ++ "</div></div></div>"
