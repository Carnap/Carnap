{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.ProofCheck (proofCheckAction) where

import Carnap.Calculi.NaturalDeduction.Syntax 
    (ProofMemoRef, NaturalDeductionCalc(..),RenderStyle(..), Inference(..))
import Carnap.Calculi.NaturalDeduction.Checker 
    (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, toDisplaySequenceMemo, toDisplaySequence)
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftLang, FixLang, CopulaSchema)
import Carnap.Core.Data.AbstractSyntaxClasses (Schematizable)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Logic as P (DerivedRule(..), propSeqParser, logicBookCalc, forallxSLCalc, propCalc, ) 
import Carnap.Languages.PureFirstOrder.Logic as FOL (DerivedRule(..),  folSeqParser, folCalc,forallxQLCalc) 
import Carnap.Languages.PureSecondOrder.Logic (msolSeqParser, msolCalc, psolSeqParser,psolCalc) 
import Carnap.Languages.PurePropositional.Util (toSchema)
import Carnap.GHCJS.SharedTypes
import Text.Parsec (parse)
import Data.IORef (IORef, newIORef,writeIORef,readIORef,modifyIORef)
import Data.Aeson as A
import qualified Data.Map as M (fromList,map) 
import Control.Lens.Fold (toListOf)
import Lib
import Carnap.GHCJS.Widget.ProofCheckBox (checkerWith, CheckerOptions(..), Button(..), CheckerFeedbackUpdate(..))
import Carnap.GHCJS.Widget.RenderDeduction
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
import Control.Monad (when)
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

-- XXX bizarre error arises when I try to send the JSON for the derived
-- rules directly. It worked on previous versions of ghcjs, so I'm going
-- to wait until I move all this to GHC 8.2 and the latest ghcjs before
-- spending too much time trying to fix.
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

data Checker r lex der = Checker 
        { checkerCalc :: NaturalDeductionCalc r lex der
        , checkerRules :: Maybe (IORef [(String,der)])
        , sequent :: Maybe (ClassicalSequentOver lex Sequent)
        , threadRef :: IORef (Maybe ThreadId)
        , proofDisplay :: Maybe Element
        , proofMemo :: ProofMemoRef lex
        }

activateChecker ::  IORef [(String,P.DerivedRule)] -> Document -> Maybe IOGoal -> IO ()
activateChecker _ _ Nothing  = return ()
activateChecker drs w (Just iog@(IOGoal i o g classes))
        | "firstOrder" `elem` classes = do
                        tryParse buildOptions folSeqParser folCalc Nothing
        | "forallxQL" `elem` classes = do
                        tryParse buildOptions folSeqParser forallxQLCalc Nothing
        | "secondOrder" `elem` classes = do
                        tryParse buildOptions msolSeqParser msolCalc (Just drs)
        | "polyadicSecondOrder" `elem` classes = do
                        tryParse buildOptions psolSeqParser psolCalc (Just drs)
        | "LogicBook" `elem` classes = do
                        tryParse buildOptions propSeqParser logicBookCalc (Just drs)
        | "forallxSL" `elem` classes = do
                        tryParse buildOptions propSeqParser forallxSLCalc (Just drs)
        | otherwise = do 
                         tryParse buildOptions propSeqParser propCalc (Just drs)
        where tryParse options seqParse calc mdrs = do
                  memo <- newIORef mempty
                  mtref <- newIORef Nothing
                  mpd <- if render options then Just <$> makeDisplay else return Nothing
                  let checker ms = threadedCheck (Checker { checkerRules = mdrs
                                                          , sequent = ms
                                                          , threadRef = mtref
                                                          , proofDisplay = mpd
                                                          , proofMemo = memo
                                                          , checkerCalc = calc})
                  mlabelseq <- if directed options then parseWith seqParse else return Nothing
                  case (submit options, mlabelseq) of
                      (Just b,Just (l,s)) -> checkerWith 
                                          (options {submit = Just b {action = trySubmit l s }})
                                          (checker (Just s))
                                          iog w
                      (Nothing,Just (l,s)) -> checkerWith 
                                          options
                                          (checker (Just s))
                                          iog w
                      _ -> checkerWith options (checker Nothing) iog w
              parseWith seqParse = do (Just gs) <- getInnerHTML g 
                                      case parse (withLabel seqParse) "" (decodeHtml gs) of
                                          Left e -> do setInnerHTML g (Just "Couldn't Parse Goal")
                                                       error "couldn't parse goal"
                                          Right (l,s) -> do setInnerHTML g (Just $ show s)
                                                            return (Just (l,s))

              makeDisplay = do (Just pd) <- createElement w (Just "div")
                               setAttribute pd "class" "proofDisplay"
                               (Just parent) <- getParentNode o
                               insertAdjacentElement (castToHTMLElement parent) "afterend" (Just pd)
                               return pd

              standardOptions = 
                    CheckerOptions { submit = Just Button { label = "Submit Solution"
                                              , action = \r w e -> return ()
                                              }
                                   , render = False
                                   , directed = True
                                   , feedback = Keypress
                                   }
              buildOptions = execState (do when ("NoSub" `elem` classes) 
                                                (modify (\o -> o {submit = Nothing}))
                                           when ("Render" `elem` classes) 
                                                (modify (\o -> o {render = True}))
                                           when ("playground" `elem` classes)
                                                (modify (\o -> o {directed = False, submit = Nothing}))
                                           when ("ruleMaker" `elem` classes)
                                                (modify (\o -> o {directed = False
                                                                 , submit = Just Button 
                                                                       { label = "Save Rule"
                                                                       , action = trySave drs
                                                                       }
                                                                 }))) standardOptions

threadedCheck checker w ref v (g, fd) = 
        do mt <- readIORef (threadRef checker)
           case mt of
               Just t -> killThread t
               Nothing -> return ()
           t' <- forkIO $ do threadDelay 200000
                             rules <- case checkerRules checker of
                                             Nothing -> return mempty
                                             Just ref -> do rlist <- liftIO $ readIORef ref
                                                            return $ M.fromList rlist
                             let ndcalc = checkerCalc checker
                             let ded = ndParseProof ndcalc rules v
                             case proofDisplay checker of 
                               Just pd -> 
                                   do renderedProof <- renderer w ded
                                      setInnerHTML pd (Just "")
                                      appendChild pd (Just renderedProof)
                               Nothing -> return Nothing
                             Feedback mseq ds <- case ndProcessLineMemo ndcalc of
                                                     Just memoline -> toDisplaySequenceMemo (memoline $ proofMemo checker) ded
                                                     Nothing -> return $ toDisplaySequence (ndProcessLine ndcalc) ded
                             ul <- genericListToUl wrap w ds
                             setInnerHTML fd (Just "")
                             appendChild fd (Just ul)
                             case sequent checker of
                                 Just s -> updateGoal s ref g mseq
                                 Nothing -> computeRule ref g mseq
           writeIORef (threadRef checker) (Just t')
           return ()

    where renderer = case ndRenderer (checkerCalc checker) of
                         MontegueStyle -> renderDeductionMontegue
                         FitchStyle -> renderDeductionFitch

updateGoal s ref g mseq = case mseq of
                         Nothing -> do setAttribute g "class" "goal"
                                       writeIORef ref False
                         (Just seq) ->  if  seq `seqSubsetUnify` s
                               then do setAttribute g "class" "goal success"
                                       writeIORef ref True
                               else do setAttribute g "class" "goal"
                                       writeIORef ref False

computeRule ref g mseq = case mseq of
                         Nothing -> do setInnerHTML g (Just "No Rule Found")
                                       writeIORef ref False
                         (Just seq) -> do setInnerHTML g (Just $ show seq)
                                          writeIORef ref True

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
                                   let Feedback mseq _ = toDisplaySequence (ndProcessLine propCalc) . ndParseProof propCalc (M.fromList rules) $ v
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

liftDerivedRules = map $ \(s,r) -> (s,liftDerivedRule r)
    where liftDerivedRule (P.DerivedRule conc prems) = FOL.DerivedRule (liftLang conc) (map liftLang prems)

errDiv :: [Char] -> [Char] -> Int -> Maybe [Char] -> [Char]
errDiv ico msg lineno (Just details) = "<div>" ++ ico ++ "<div><div>Error on line " 
                                       ++ show lineno ++ ": " ++ msg 
                                       ++ "<div>see details<div>" 
                                       ++ details 
                                       ++ "</div></div></div></div></div>"
errDiv ico msg lineno Nothing = "<div>" ++ ico ++ "<div><div>Error on line " 
                              ++ show lineno ++ ": " ++ msg 
                              ++ "</div></div></div>"
