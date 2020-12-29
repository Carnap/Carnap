{-#LANGUAGE FlexibleContexts, RankNTypes #-}
module Carnap.GHCJS.Action.ProofCheck (proofCheckAction) where

import Carnap.Calculi.NaturalDeduction.Syntax 
    (ProofMemoRef, NaturalDeductionCalc(..),RenderStyle(..), Inference(..), RuntimeNaturalDeductionConfig(..), Deduction)
import Carnap.Calculi.NaturalDeduction.Checker 
    (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, toDisplaySequenceMemo, toDisplaySequence)
import Carnap.Core.Data.Optics (liftLang, PrismSubstitutionalVariable, PrismLink)
import Carnap.Core.Data.Classes (Handed(..))
import Carnap.Core.Unification.Unification (MonadVar)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses (ToSchema(..))
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PureFirstOrder.Logic 
import Carnap.Languages.ModalPropositional.Logic (ofModalPropSys)
import Carnap.Languages.PureSecondOrder.Logic (ofSecondOrderSys) 
import Carnap.Languages.SetTheory.Logic (ofSetTheorySys)
import Carnap.Languages.DefiniteDescription.Logic.Gamut (ofDefiniteDescSys)
import Carnap.Languages.ModalFirstOrder.Logic (hardegreeMPLCalc)
import Carnap.GHCJS.SharedTypes
import Text.Parsec (parse)
import Data.IORef (IORef, newIORef,writeIORef, readIORef, modifyIORef)
import Data.Aeson as A
import Data.Text (pack)
import Data.Maybe (catMaybes)
import qualified Data.Map as M (lookup,fromList,toList,map) 
import Control.Lens.Fold (toListOf,(^?))
import Lib
import Lib.FormulaTests
import Carnap.GHCJS.Widget.ProofCheckBox (checkerWith, CheckerOptions(..), CheckerFeedbackUpdate(..), optionsFromMap, Button(..) )
import Carnap.GHCJS.Widget.RenderDeduction
import GHCJS.DOM.Element (setInnerHTML, getInnerHTML, setAttribute, mouseOver, mouseOut)
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
import GHCJS.DOM.EventM (EventM, eventCurrentTarget, newListener, addListener)
import GHCJS.DOM.Window (prompt)
import GHCJS.DOM.Node (appendChild, getParentNode, removeChild, getParentElement)
--import GHCJS.DOM.EventM
import Control.Monad (when,mplus)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (modify,get,execState,State)
import Control.Concurrent
import Data.Typeable

proofCheckAction :: IO ()
proofCheckAction = do availableDerived <- newIORef []
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
addRules :: IORef [(String, SomeRule)] -> Value -> IO ()
addRules avd v =  case fromJSON v :: Result String of
                    A.Error e -> do print $ "error decoding derived rules: " ++ e
                                    print $ "recieved string: " ++ show v
                    Success s -> do let v' = read s :: Value
                                    case fromJSON v' :: Result [(String,SomeRule)] of
                                          A.Error e -> do print $ "error decoding derived rules: " ++ e
                                                          print $ "recieved JSON: " ++ show v
                                          Success rs -> do print $ show rs
                                                           writeIORef avd rs

getCheckers :: IsElement self => Document -> self -> IO [Maybe IOGoal]
getCheckers w = generateExerciseElts w "proofchecker"

data Checker r lex sem = Checker 
        { checkerToRule :: Maybe (DerivedRule lex sem -> SomeRule)
        , checkerTests :: Maybe ([String] -> UnaryTest lex sem)
        , ruleSave' :: Maybe (Checker r lex sem -> IORef [(String, SomeRule)] -> IORef Bool -> Document -> Element -> EventM Element MouseEvent ())
        , rulePost' :: Checker r lex sem -> IO (RuntimeNaturalDeductionConfig lex sem)
        , checkerCalc ::  NaturalDeductionCalc r lex sem 
        , checkerRules :: IORef [(String,SomeRule)]
        , sequent :: Maybe (ClassicalSequentOver lex (Sequent sem))
        , threadRef :: IORef (Maybe ThreadId)
        , proofDisplay :: Maybe Element
        , proofMemo :: ProofMemoRef lex sem r
        }

rulePost x = rulePost' x x 

ruleSave x = case ruleSave' x of 
    Just f -> f x
    Nothing -> \_ _ _ _ -> liftIO $ message "Can't save: this calculus doesn't have derived rules"

activateChecker ::  IORef [(String,SomeRule)] -> Document -> Maybe IOGoal -> IO ()
activateChecker _ _ Nothing  = return ()
activateChecker drs w (Just iog@(IOGoal i o g _ opts)) -- TODO: need to update non-montague calculi to take first/higher-order derived rules
        | sys == "prop"                      = tryParse propCalc (propChecker (Just trySave))
        | sys == "firstOrder"                = tryParse folCalc (folChecker (Just trySave))
        | sys == "hardegreeMPL"              = tryParse hardegreeMPLCalc noRuntimeOptions
        | otherwise = maybe noSystem id $ ((\it -> tryParse it $ propChecker Nothing) `ofPropSys` sys)
                                     `mplus` ((\it -> tryParse it $ folChecker Nothing) `ofFOLSys` sys)
                                     `mplus` ((\it -> tryParse it noRuntimeOptions) `ofSecondOrderSys` sys)
                                     `mplus` ((\it -> tryParse it noRuntimeOptions) `ofSetTheorySys` sys)
                                     `mplus` ((\it -> tryParse it noRuntimeOptions) `ofDefiniteDescSys` sys)
                                     `mplus` ((\it -> tryParse it noRuntimeOptions) `ofModalPropSys` sys)
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "prop"

              noSystem = do setInnerHTML g (Just $ "Can't find a formal system named " ++ sys)
                            error $ "couldn't find formal system:" ++ sys

              tryParse calc checker = do
                  memo <- newIORef mempty
                  mtref <- newIORef Nothing
                  mpd <- if render options then Just <$> makeDisplay else return Nothing
                  mseq <- if directed options then parseGoal calc else return Nothing
                  let theChecker = checker calc drs mseq mtref mpd memo
                      checkSeq = threadedCheck options theChecker
                      saveProblem l s = Button {label = "Submit" , action = submitDer w opts theChecker l g s}
                      saveRule = Button {label = "Save" , action = ruleSave theChecker drs}
                      options' = options { submit = case (M.lookup "submission" opts, M.lookup "goal" opts) of
                                                      (Just "saveRule",_) -> Just saveRule
                                                      (Just s, Just g) | take 7 s == "saveAs:" -> Just $ saveProblem (drop 7 s) (theSeq g)
                                                      _ -> Nothing
                                         }
                  checkerWith options' checkSeq iog w
                  
                  where options = optionsFromMap opts
                        theSeq g = case parse (ndParseSeq calc) "" g of
                                       Left e -> error "couldn't parse goal"
                                       Right seq -> seq

              parseGoal calc = do let seqParse = ndParseSeq calc
                                      Just seqstring = M.lookup "goal" opts 
                                      --XXX: the directed option is set by the existence of a goal, so this match can't fail.
                                  case parse seqParse "" seqstring of
                                      Left e -> do setInnerHTML g (Just $ "Couldn't Parse This Goal:" ++ seqstring)
                                                   error "couldn't parse goal"
                                      Right seq -> do setInnerHTML g (Just $ ndNotation calc $ show seq)
                                                      return $ Just seq
                                                              
              makeDisplay = do (Just pd) <- createElement w (Just "div")
                               setAttribute pd "class" "proofDisplay"
                               Just parent <- getParentNode o
                               insertAdjacentElement (castToHTMLElement parent) "afterend" (Just pd)
                               return pd

              --XXX:DRY this pattern
              propChecker x = Checker (Just PropRule) (Just propTests) x
                                    $ \self -> do somerules <- readIORef (checkerRules self)
                                                  let seqrules = catMaybes $ map readyRule somerules
                                                      rmap = M.fromList seqrules
                                                      premseqs = toPremiseSeqs . sequent $ self
                                                  return $ RuntimeNaturalDeductionConfig rmap premseqs
                    where readyRule (x, PropRule r) = Just (x, derivedRuleToSequent r)
                          readyRule _ = Nothing

              folChecker x = Checker (Just FOLRule) (Just folTests) x
                                   $ \self -> do somerules <- readIORef (checkerRules self)
                                                 let seqrules = catMaybes $ map readyRule somerules
                                                     rmap = M.fromList seqrules
                                                     premseqs = toPremiseSeqs . sequent $ self
                                                 return $ RuntimeNaturalDeductionConfig rmap premseqs
                    where readyRule (x, PropRule r) = Just (x, liftSequent . derivedRuleToSequent $ r)
                          readyRule (x, FOLRule r) = Just (x, derivedRuleToSequent r)
                          readyRule _ = Nothing

              toPremiseSeqs :: (Concretes lex b, Typeable b) => Maybe (ClassicalSequentOver lex (Sequent b)) -> Maybe [ClassicalSequentOver lex (Sequent b)]
              toPremiseSeqs (Just seq) = Just . map (\x -> SA x :|-: SS x) $ toListOf (lhs . concretes) seq
              toPremiseSeqs Nothing = Nothing

              noRuntimeOptions = Checker Nothing Nothing Nothing $ const . pure $ RuntimeNaturalDeductionConfig mempty mempty

threadedCheck options checker w ref v (g, fd) = 
        do mt <- readIORef (threadRef checker)
           case mt of
               Just t -> killThread t
               Nothing -> return ()
           t' <- forkIO $ do setAttribute g "class" "goal working"
                             threadDelay 500000
                             rtconfig <- liftIO $ rulePost checker
                             let ndcalc = checkerCalc checker
                                 ded = ndParseProof ndcalc rtconfig v
                             case proofDisplay checker of 
                               Just pd -> 
                                   do renderedProof <- renderer w ndcalc ded
                                      setInnerHTML pd (Just "")
                                      appendChild pd (Just renderedProof)
                               Nothing -> return Nothing
                             Feedback mseq ds <- getFeedback checker ded
                             ul <- case feedback options of
                                       SyntaxOnly -> genericListToUl (syntaxwrap fd w) w ds
                                       _ -> genericListToUl (wrap fd w ndcalc) w ds
                             setInnerHTML fd (Just "")
                             appendChild fd (Just ul)
                             Just wrapper <- getParentElement g
                             --XXX: the check below could be inlined better
                             case tests options of 
                                [] -> case sequent checker of
                                    Just s -> updateGoal w s ref g wrapper mseq options
                                    Nothing -> computeRule ref g mseq ndcalc
                                t -> case checkerTests checker of
                                    Just fts -> applyTests (fts t) ref g mseq wrapper options
           writeIORef (threadRef checker) (Just t')
           return ()

    where renderer = case ndRenderer (checkerCalc checker) of
                         MontagueStyle -> renderDeductionMontague 
                         FitchStyle _ -> renderDeductionFitch 
                         LemmonStyle _ -> renderDeductionLemmon
                         NoRender -> renderNull

updateGoal w s ref g wrapper mseq options = 
        case (mseq, feedback options) of
             (Nothing,_) -> setAttribute g "class" "goal" >> setAttribute wrapper "class" "" >> writeIORef ref False
             (Just seq, SyntaxOnly) -> setAttribute g "class" "goal" >> setAttribute wrapper "class" "" >> writeIORef ref (seq `seqSubsetUnify` s)
             (Just seq, _) | seq `seqSubsetUnify` s -> setAttribute g "class" "goal success" >> setSuccess w wrapper >> writeIORef ref True
             _ -> setAttribute g "class" "goal" >> setFailure w wrapper >> writeIORef ref False

applyTests :: Sequentable lex => UnaryTest lex sem -> IORef Bool -> Element 
                    -> Maybe (ClassicalSequentOver lex (Sequent sem)) -> Element -> CheckerOptions -> IO ()
applyTests theTests ref g mseq wrapper options =
        case mseq of 
            Nothing -> setAttribute g "class" "goal" >> setAttribute wrapper "class" "" >> writeIORef ref False
            Just (_:|-: (SS f))-> case (theTests (fromSequent f), feedback options) of
                 (Nothing, SyntaxOnly) -> writeIORef ref True
                 (Just s, SyntaxOnly) -> writeIORef ref False
                 (Nothing, _) -> setAttribute g "class" "goal success" >> setAttribute wrapper "class" "success" >> writeIORef ref True
                 (Just s, _) -> do
                     alerts <- getListOfElementsByClass g "incompleteAlert"
                     case alerts of
                         (Just alert):_ -> setAttribute alert "title" s --XXX popper displays title attribute if any is given
                         _ -> return ()
                     setAttribute g "class" "goal" >> setAttribute wrapper "class" "failure" >> writeIORef ref False

computeRule ref g mseq calc = 
        case mseq of
           Nothing -> do setInnerHTML g (Just "No Rule Found")
                         writeIORef ref False
           (Just seq) -> do setInnerHTML g (Just $ ndNotation calc $ show seq)
                            writeIORef ref True

submitDer w opts checker l g seq ref _ i = do 
        isFinished <- liftIO $ readIORef ref
        Just v <- liftIO $ getValue (castToHTMLTextAreaElement i)
        Just wrap <- getParentElement i
        if isFinished 
            then trySubmit w Derivation opts l (DerivationDataOpts (pack $ show seq) (pack v) (M.toList opts)) True
            else do liftIO $ setAttribute g "class" "goal working"
                    rtconfig <- liftIO $ rulePost checker
                    let ndcalc = checkerCalc checker
                        ded = ndParseProof ndcalc rtconfig v
                        submission = DerivationDataOpts (pack $ show seq) (pack v) (M.toList opts)
                    Feedback mseq _ <- liftIO $ getFeedback checker ded
                    setAttribute g "class" "goal"
                    case sequent checker of
                         Nothing -> message "No goal sequent to submit"
                         Just s -> case mseq of 
                             (Just s') --we allow feedback in syntax-only mode here, since in non-exam mode, you can figure out whether you were right anyway.
                               | "exam" `inOpts` opts -> trySubmit w Derivation opts l submission (s' `seqSubsetUnify` s)
                               | (s' `seqSubsetUnify` s) -> trySubmit w Derivation opts l submission True  >> setSuccess w wrap
                               | otherwise -> message "not yet finished" >> setFailure w wrap 
                             _ | "exam" `inOpts` opts -> trySubmit w Derivation opts l submission False
                               | otherwise -> message "not yet finished" >> setFailure w wrap

trySave :: ( Sequentable lex
           , Inference r lex sem
           , ToSchema lex sem
           , PrismSubstitutionalVariable lex
           , MonadVar (ClassicalSequentOver lex) (State Int)
           , Concretes lex sem
           ) => Checker r lex sem -> IORef [(String, SomeRule)] -> IORef Bool -> Document
                -> Element -> EventM e MouseEvent ()
trySave checker drs ref w i = 
        do isFinished <- liftIO $ readIORef ref
           somerules <- liftIO $ readIORef drs
           rtconfig <- liftIO $ rulePost checker
           Just view <- getDefaultView w
           if isFinished
             then do (Just v) <- getValue (castToHTMLTextAreaElement i)
                     let ndcalc = checkerCalc checker
                         ded = ndParseProof ndcalc rtconfig v
                     Feedback mseq _ <- liftIO $ getFeedback checker ded 
                     case mseq of
                      Nothing -> message "A rule can't be extracted from this proof"
                      (Just (a :|-: c)) -> do
                          -- XXX : throw a more transparent error here if necessary
                          let prems = map (toSchema . fromSequent) (toListOf concretes a)
                          case c ^? concretes of
                              Nothing -> error "The formula type couldn't be decoded."
                              Just c' -> do
                                  let conc = (toSchema . fromSequent) c'
                                  mname <- prompt view "What name will you give this rule (use all capital letters!)" (Just "")
                                  case (mname,checkerToRule checker)  of
                                      (Just name, Just toRule) | allcaps name -> do
                                            Just t <- eventCurrentTarget
                                            liftIO $ sendJSON (SaveRule name $ toRule $ DerivedRule conc prems) 
                                                              (loginCheck $ setStatus w (castToElement t) Submitted) 
                                                              error
                                      (Just name, Just toRule) -> message "rule name must be all capital letters"
                                      (Nothing,_) -> message "No name entered"
                                      (_,Nothing) -> message "No saved rules for this proof system"
             else message "not yet finished"
    where loginCheck callback c | c == "No User" = message "You need to log in before you can save a rule"
                                | c == "Clash"   = message "it appears you've already got a rule with this name"
                                | otherwise      = message "Saved your new rule!" >> callback >> reloadPage
          error c = message ("Something has gone wrong. Here's the error: " ++ c)
          allcaps s = and (map (`elem` "ABCDEFGHIJKLMNOPQRSTUVWXYZ") s)

-------------------------
--  Utility Functions  --
-------------------------

getFeedback :: ( PrismSubstitutionalVariable lex
               , MonadVar (ClassicalSequentOver lex) (State Int)
               , Inference r lex sem
               , Sequentable lex
               ) => Checker r lex sem -> Deduction r lex sem -> IO (Feedback lex sem)
getFeedback checker ded = case ndProcessLineMemo calc of
                                     Just memoline -> toDisplaySequenceMemo (memoline $ proofMemo checker) ded
                                     Nothing -> return $ toDisplaySequence (ndProcessLine calc) ded
    where calc = checkerCalc checker

configFrom rules prems = RuntimeNaturalDeductionConfig (M.fromList . map (\(x,y) -> (x,derivedRuleToSequent y)) $ rules) prems

wrap fd w calc elt (Right s) = popUpWith fd w elt "+" (ndNotation calc $ show s) Nothing
wrap fd w _ elt (Left (GenericError s n)) = popUpWith fd w elt "?" ("Error on line " ++ show n ++ ": " ++ s) Nothing
wrap fd w _ elt (Left (NoParse e n)) = popUpWith fd w elt "⚠" ("Can't read line " ++ show n ++ ". There may be a typo.") (Just . cleanIt . show $ e)
    where chunks s = case break (== '\"') s of 
                            (l,[]) -> l:[]
                            (l,_:s') -> l:chunks s'
          cleanChunk c = case (readMaybe $ "\"" ++ c ++ "\"") :: Maybe String of 
                            Just s -> s
                            Nothing -> c
          cleanIt = concat . map cleanChunk . chunks 

          readMaybe s = case reads s of
                          [(x, "")] -> Just x
                          _ -> Nothing
wrap fd w calc elt (Left (NoUnify eqs n)) = 
        popUpWith fd w elt "✗" ("Error on line " ++ show n ++ ". Can't match these premises with this conclusion, using this rule.") 
                               (Just $ ndNotation calc $ toUniErr eqs)
wrap fd w _ elt (Left (NoResult _)) = setInnerHTML elt (Just "&nbsp;")

syntaxwrap fd w elt (Left (NoParse e n)) = popUpWith fd w elt "⚠" ("Can't read line " ++ show n ++ ". There may be a typo.") (Just . cleanString . show $ e)
syntaxwrap fd w elt (Left (NoResult _))  = setInnerHTML elt (Just "&nbsp;")
syntaxwrap fd w elt _ = setInnerHTML elt (Just "-")

toUniErr eqs = "In order to apply this inference rule, there needs to be a substitution that makes at least one of these sets of pairings match:" 
                ++ (concat $ map endiv' $ map (concat . map (endiv . show) . reverse) eqs)
                -- TODO make this less horrible, give equations internal
                -- structure so that they can be aligned properly
    where endiv e = "<div>" ++ e ++ "</div>"
          endiv' e = "<div class=\"equations\">" ++ e ++ "</div>"

errDiv :: String -> String -> Int -> Maybe String -> String
errDiv ico msg lineno (Just details) = "<div>" ++ ico ++ "<div><div>Error on line " 
                                       ++ show lineno ++ ": " ++ msg 
                                       ++ "<div>" 
                                       ++ details 
                                       ++ "</div></div></div></div>"
errDiv ico msg lineno Nothing = "<div>" ++ ico ++ "<div><div>Error on line " 
                              ++ show lineno ++ ": " ++ msg 
                              ++ "</div></div></div>"
