{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.ProofCheck (proofCheckAction) where

import Carnap.Calculi.NaturalDeduction.Syntax 
    (ProofMemoRef, NaturalDeductionCalc(..),RenderStyle(..), Inference(..))
import Carnap.Calculi.NaturalDeduction.Checker 
    (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, toDisplaySequenceMemo, toDisplaySequence)
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftLang, FixLang, CopulaSchema)
import Carnap.Core.Data.AbstractSyntaxClasses (Schematizable)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Logic as P 
    (DerivedRule(..), logicBookCalc, magnusSLCalc, magnusSLPlusCalc, propCalc, hardegreeSLCalc
    , thomasBolducAndZachTFLCalc) 
import Carnap.Languages.PureFirstOrder.Logic as FOL 
    (DerivedRule(..), folCalc, magnusQLCalc
    , thomasBolducAndZachFOLCalc, hardegreePLCalc) 
import Carnap.Languages.ModalPropositional.Logic as MPL
    ( hardegreeWTLCalc, hardegreeLCalc, hardegreeKCalc, hardegreeTCalc
    , hardegreeBCalc, hardegreeDCalc, hardegreeFourCalc, hardegreeFiveCalc)
import Carnap.Languages.PureSecondOrder.Logic 
    (msolCalc, psolCalc) 
import Carnap.Languages.ModalFirstOrder.Logic
    ( hardegreeMPLCalc )
import Carnap.Languages.PurePropositional.Util (toSchema)
import Carnap.GHCJS.SharedTypes
import Text.Parsec (parse)
import Data.IORef (IORef, newIORef,writeIORef, readIORef, modifyIORef)
import Data.Aeson as A
import qualified Data.Map as M (lookup,fromList,map) 
import Control.Lens.Fold (toListOf,(^?))
import Lib
import Carnap.GHCJS.Widget.ProofCheckBox (checkerWith, CheckerOptions(..), Button(..), CheckerFeedbackUpdate(..))
import Carnap.GHCJS.Widget.RenderDeduction
import GHCJS.DOM.Element (setInnerHTML,getInnerHTML, setAttribute,mouseOver,mouseOut)
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
import GHCJS.DOM.EventM (EventM, target, newListener,addListener)
import GHCJS.DOM.Window (prompt)
import GHCJS.DOM.Node (appendChild, getParentNode,removeChild)
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

getCheckers :: IsElement self => Document -> self -> IO [Maybe IOGoal]
getCheckers w = generateExerciseElts w "proofchecker"

data Checker r lex sem der = Checker 
        { rulePost :: IORef [(String,P.DerivedRule)] -> IO [(String,der)]
        , checkerCalc :: NaturalDeductionCalc r lex sem der
        , checkerRules :: IORef [(String,P.DerivedRule)]
        , sequent :: Maybe (ClassicalSequentOver lex (Sequent sem))
        , threadRef :: IORef (Maybe ThreadId)
        , proofDisplay :: Maybe Element
        , proofMemo :: ProofMemoRef lex sem r
        }

activateChecker ::  IORef [(String,P.DerivedRule)] -> Document -> Maybe IOGoal -> IO ()
activateChecker _ _ Nothing  = return ()
activateChecker drs w (Just iog@(IOGoal i o g _ opts)) -- TODO: need to update non-montegue calculi to take first/higher-order derived rules
        | sys == "prop"                      = tryParse propCalc propChecker
        | sys == "firstOrder"                = tryParse folCalc folChecker
        | sys == "secondOrder"               = tryParse msolCalc propChecker
        | sys == "polyadicSecondOrder"       = tryParse psolCalc propChecker
        | sys == "LogicBook"                 = tryParse logicBookCalc propChecker
        | sys == "magnusSL"                  = tryParse magnusSLCalc propChecker
        | sys == "magnusSLPlus"              = tryParse magnusSLPlusCalc propChecker
        | sys == "magnusQL"                  = tryParse magnusQLCalc propChecker
        | sys == "thomasBolducAndZachTFL"    = tryParse thomasBolducAndZachTFLCalc propChecker
        | sys == "thomasBolducAndZachFOL"    = tryParse thomasBolducAndZachFOLCalc propChecker
        | sys == "hardegreeSL"               = tryParse hardegreeSLCalc propChecker
        | sys == "hardegreePL"               = tryParse hardegreePLCalc propChecker
        | sys == "hardegreeWTL"              = tryParse hardegreeWTLCalc propChecker
        | sys == "hardegreeL"                = tryParse hardegreeLCalc propChecker
        | sys == "hardegreeK"                = tryParse hardegreeKCalc propChecker
        | sys == "hardegreeD"                = tryParse hardegreeDCalc propChecker
        | sys == "hardegreeT"                = tryParse hardegreeTCalc propChecker
        | sys == "hardegreeB"                = tryParse hardegreeBCalc propChecker
        | sys == "hardegree4"                = tryParse hardegreeFourCalc propChecker
        | sys == "hardegree5"                = tryParse hardegreeFiveCalc propChecker
        | sys == "hardegreeMPL"              = tryParse hardegreeMPLCalc folChecker
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "prop"
              tryParse calc checker = do
                  memo <- newIORef mempty
                  mtref <- newIORef Nothing
                  mpd <- if render options then Just <$> makeDisplay else return Nothing
                  let checkSeq ms = threadedCheck (checker calc drs ms mtref mpd memo)
                  mseq <- if directed options then parseGoal calc else return Nothing
                  checkerWith options (checkSeq mseq) iog w
              parseGoal calc = do let seqParse = ndParseSeq calc
                                      (Just seqstring) = M.lookup "goal" opts 
                                      --XXX: the directed option is set by the existence of a goal, so this match can't fail.
                                  case parse seqParse "" seqstring of
                                      Left e -> do setInnerHTML g (Just $ "Couldn't Parse This Goal:" ++ seqstring)
                                                   error "couldn't parse goal"
                                      Right seq -> do setInnerHTML g (Just $ show seq)
                                                      return $ Just seq
              makeDisplay = do (Just pd) <- createElement w (Just "div")
                               setAttribute pd "class" "proofDisplay"
                               (Just parent) <- getParentNode o
                               insertAdjacentElement (castToHTMLElement parent) "afterend" (Just pd)
                               return pd

              propChecker = Checker readIORef

              folChecker = Checker (\ref -> liftDerivedRules <$> readIORef ref)

              options = CheckerOptions { submit = case (M.lookup "submission" opts, M.lookup "goal" opts) of
                                                        (Just "saveRule",_) -> Just saveRule
                                                        (Just s, Just g) | take 7 s == "saveAs:" -> Just $ saveProblem (drop 7 s) g
                                                        _ -> Nothing
                                       , feedback = case M.lookup "feedback" opts of
                                                        Just "manual" -> Click
                                                        Just "none" -> Never
                                                        _ -> Keypress
                                       , directed = case M.lookup "goal" opts of
                                                        Just _ -> True
                                                        Nothing -> False
                                       , initialUpdate = False
                                       , indentGuides = "guides" `elem` options
                                       , render = "render" `elem` options
                                       }
                                where -- options = [ ("NoSub", \o -> o {submit = Nothing})
                                      --           , ("Render", \o -> o {render = True})
                                      --           , ("playground", \o -> o {directed = False, submit = Nothing})
                                      --           , ("ruleMaker", \o -> o {directed = False , submit = Just saveButton })
                                      --           , ("manualFeedback", \o -> o {feedback = Click})
                                      --           , ("noFeedback", \o -> o {feedback = Never})
                                      --           , ("guides", \o -> o {indentGuides = True})
                                      --           ]
                                      saveRule = Button {label = "Save Rule" , action = trySave drs}
                                      saveProblem l s = Button {label = "Submit Solution" , action = trySubmit l s}
                                      options = case M.lookup "options" opts of Just s -> words s; Nothing -> []

threadedCheck checker w ref v (g, fd) = 
        do mt <- readIORef (threadRef checker)
           case mt of
               Just t -> killThread t
               Nothing -> return ()
           t' <- forkIO $ do setAttribute g "class" "goal working"
                             threadDelay 500000
                             rules <- do rlist <- liftIO $ (rulePost checker) (checkerRules checker)
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
                             ul <- genericListToUl (wrap fd w) w ds
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
                         (Just seq) -> if seq `seqSubsetUnify` s
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
                                                        (SubmitDerivation (l ++ ":" ++ s) v source key) 
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
                                    (Just (a :|-: c)) -> do
                                        -- XXX : throw a more transparent error here if necessary
                                        let prems = map (toSchema . fromSequent) (toListOf concretes a)
                                        case c ^? concretes of
                                            Nothing -> error "The formula type couldn't be decoded."
                                            Just c' -> do
                                                let conc = (toSchema . fromSequent) c'
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

wrap fd w elt (Right s)                  = popUpWith fd w elt "+" (show s) Nothing
wrap fd w elt (Left (GenericError s n))  = popUpWith fd w elt "?" ("Error on line " ++ show n ++ ": " ++ s) Nothing
wrap fd w elt (Left (NoParse e n))       = popUpWith fd w elt "⚠" ("Can't read line " ++ show n ++ ". There may be a typo.") (Just $ show e)
wrap fd w elt (Left (NoUnify eqs n))     = popUpWith fd w elt "✗" ("Error on line " ++ show n ++ ". Can't match these premises with this conclusion, using this rule.") (Just $ toUniErr eqs)
wrap fd w elt (Left (NoResult _))        = setInnerHTML elt (Just "&nbsp;")

popUpWith :: Element -> Document -> Element -> String -> String -> Maybe String -> IO ()
popUpWith fd w elt label msg details = 
        do setInnerHTML elt (Just label)
           (Just outerpopper) <- createElement w (Just "div")
           (Just innerpopper) <- createElement w (Just "div")
           setAttribute innerpopper "class" "popper"
           setInnerHTML innerpopper (Just msg)
           appendChild outerpopper (Just innerpopper)
           case details of 
            Just deets -> do
               (Just detailpopper) <- createElement w (Just "div")
               setAttribute detailpopper "class" "details"
               setInnerHTML detailpopper (Just deets)
               appendChild innerpopper (Just detailpopper)
               return ()
            Nothing -> return ()
           (Just p) <- getParentNode fd
           (Just gp) <- getParentNode p
           appender <- newListener $ appendPopper outerpopper gp
           remover <- newListener $ removePopper outerpopper gp
           addListener elt mouseOver appender False
           addListener elt mouseOut remover False
    where appendPopper pop targ = do liftIO $ appendChild targ (Just pop) 
                                     liftIO $ makePopper elt pop
          removePopper pop targ = do liftIO $ removeChild targ (Just pop)
                                     return ()

toUniErr eqs = "In order to apply this inference rule, there needs to be a substitution that makes at least one of these sets of pairings match:" 
                ++ (concat $ map endiv' $ map (concat . map (endiv . show) . reverse) eqs)
                -- TODO make this less horrible, give equations internal
                -- structure so that they can be aligned properly
    where endiv e = "<div>" ++ e ++ "</div>"
          endiv' e = "<div class=\"equations\">" ++ e ++ "</div>"

liftDerivedRules = map $ \(s,r) -> (s,liftDerivedRule r)
    where liftDerivedRule (P.DerivedRule conc prems) = FOL.DerivedRule (liftLang conc) (map liftLang prems)

errDiv :: String -> String -> Int -> Maybe String -> String
errDiv ico msg lineno (Just details) = "<div>" ++ ico ++ "<div><div>Error on line " 
                                       ++ show lineno ++ ": " ++ msg 
                                       ++ "<div>" 
                                       ++ details 
                                       ++ "</div></div></div></div>"
errDiv ico msg lineno Nothing = "<div>" ++ ico ++ "<div><div>Error on line " 
                              ++ show lineno ++ ": " ++ msg 
                              ++ "</div></div></div>"
