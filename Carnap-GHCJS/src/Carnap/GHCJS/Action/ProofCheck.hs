{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.ProofCheck (proofCheckAction) where

import Carnap.Calculi.NaturalDeduction.Syntax 
    (ProofMemoRef, NaturalDeductionCalc(..),RenderStyle(..), Inference(..), RuntimeNaturalDeductionConfig(..))
import Carnap.Calculi.NaturalDeduction.Checker 
    (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, toDisplaySequenceMemo, toDisplaySequence)
import Carnap.Core.Data.Optics (liftLang)
import Carnap.Core.Data.Classes (Handed(..))
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Logic as P 
    ( DerivedRule(..), propCalc, logicBookSDCalc, logicBookSDPlusCalc, magnusSLCalc
    , magnusSLPlusCalc, montagueSCCalc, hardegreeSLCalc, hausmanSLCalc
    , thomasBolducAndZachTFLCalc, tomassiPLCalc)
import Carnap.Languages.PurePropositional.Logic.Rules (derivedRuleToSequent)
import Carnap.Languages.PureFirstOrder.Logic as FOL 
    ( DerivedRule(..), folCalc, montagueQCCalc, magnusQLCalc , thomasBolducAndZachFOLCalc
    , hardegreePLCalc , goldfarbNDCalc, goldfarbAltNDCalc
    , goldfarbNDPlusCalc, goldfarbAltNDPlusCalc , logicBookPDPlusCalc
    , logicBookPDCalc) 
import Carnap.Languages.ModalPropositional.Logic as MPL
    ( hardegreeWTLCalc, hardegreeLCalc, hardegreeKCalc, hardegreeTCalc
    , hardegreeBCalc, hardegreeDCalc, hardegreeFourCalc, hardegreeFiveCalc)
import Carnap.Languages.PureSecondOrder.Logic 
    (msolCalc, psolCalc) 
import Carnap.Languages.SetTheory.Logic.Carnap
    (estCalc, sstCalc)
import Carnap.Languages.ModalFirstOrder.Logic
    ( hardegreeMPLCalc )
import Carnap.Languages.PurePropositional.Util (toSchema)
import Carnap.GHCJS.SharedTypes
import Text.Parsec (parse)
import Data.IORef (IORef, newIORef,writeIORef, readIORef, modifyIORef)
import Data.Aeson as A
import Data.Text (pack)
import qualified Data.Map as M (lookup,fromList,toList,map) 
import Control.Lens.Fold (toListOf,(^?))
import Lib
import Carnap.GHCJS.Widget.ProofCheckBox (checkerWith, CheckerOptions(..), CheckerFeedbackUpdate(..), optionsFromMap, Button(..) )
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

data Checker r lex sem = Checker 
        { rulePost' :: Checker r lex sem -> IO (RuntimeNaturalDeductionConfig lex sem)
        , checkerCalc :: NaturalDeductionCalc r lex sem 
        , checkerRules :: IORef [(String,P.DerivedRule)]
        , sequent :: Maybe (ClassicalSequentOver lex (Sequent sem))
        , threadRef :: IORef (Maybe ThreadId)
        , proofDisplay :: Maybe Element
        , proofMemo :: ProofMemoRef lex sem r
        }

rulePost x = rulePost' x x 

activateChecker ::  IORef [(String,P.DerivedRule)] -> Document -> Maybe IOGoal -> IO ()
activateChecker _ _ Nothing  = return ()
activateChecker drs w (Just iog@(IOGoal i o g _ opts)) -- TODO: need to update non-montague calculi to take first/higher-order derived rules
        | sys == "prop"                      = tryParse propCalc propChecker
        | sys == "firstOrder"                = tryParse folCalc folChecker
        | sys == "secondOrder"               = tryParse msolCalc noRuntimeOptions
        | sys == "polyadicSecondOrder"       = tryParse psolCalc noRuntimeOptions
        | sys == "elementarySetTheory"       = tryParse estCalc noRuntimeOptions
        | sys == "separativeSetTheory"       = tryParse sstCalc noRuntimeOptions
        | sys == "montagueSC"                = tryParse montagueSCCalc propChecker
        | sys == "montagueQC"                = tryParse montagueQCCalc folChecker
        | sys == "LogicBookSD"               = tryParse logicBookSDCalc propChecker
        | sys == "LogicBookSDPlus"           = tryParse logicBookSDPlusCalc propChecker
        | sys == "LogicBookPD"               = tryParse logicBookPDCalc folChecker
        | sys == "LogicBookPDPlus"           = tryParse logicBookPDPlusCalc folChecker
        | sys == "hausmanSL"                 = tryParse hausmanSLCalc propChecker
        | sys == "magnusSL"                  = tryParse magnusSLCalc propChecker
        | sys == "magnusSLPlus"              = tryParse magnusSLPlusCalc propChecker
        | sys == "magnusQL"                  = tryParse magnusQLCalc folChecker
        | sys == "goldfarbND"                = tryParse goldfarbNDCalc folChecker
        | sys == "goldfarbAltND"             = tryParse goldfarbAltNDCalc folChecker
        | sys == "goldfarbNDPlus"            = tryParse goldfarbNDPlusCalc folChecker
        | sys == "goldfarbAltNDPlus"         = tryParse goldfarbAltNDPlusCalc folChecker
        | sys == "thomasBolducAndZachTFL"    = tryParse thomasBolducAndZachTFLCalc propChecker
        | sys == "thomasBolducAndZachFOL"    = tryParse thomasBolducAndZachFOLCalc folChecker
        | sys == "tomassiPL"                 = tryParse tomassiPLCalc propChecker
        | sys == "hardegreeSL"               = tryParse hardegreeSLCalc propChecker
        | sys == "hardegreePL"               = tryParse hardegreePLCalc noRuntimeOptions
        | sys == "hardegreeWTL"              = tryParse hardegreeWTLCalc noRuntimeOptions
        | sys == "hardegreeL"                = tryParse hardegreeLCalc noRuntimeOptions
        | sys == "hardegreeK"                = tryParse hardegreeKCalc noRuntimeOptions
        | sys == "hardegreeD"                = tryParse hardegreeDCalc noRuntimeOptions
        | sys == "hardegreeT"                = tryParse hardegreeTCalc noRuntimeOptions
        | sys == "hardegreeB"                = tryParse hardegreeBCalc noRuntimeOptions
        | sys == "hardegree4"                = tryParse hardegreeFourCalc noRuntimeOptions
        | sys == "hardegree5"                = tryParse hardegreeFiveCalc noRuntimeOptions
        | sys == "hardegreeMPL"              = tryParse hardegreeMPLCalc noRuntimeOptions
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "prop"
              tryParse calc checker = do
                  memo <- newIORef mempty
                  mtref <- newIORef Nothing
                  mpd <- if render options then Just <$> makeDisplay else return Nothing
                  mseq <- if directed options then parseGoal options calc else return Nothing
                  let theChecker = checker calc drs mseq mtref mpd memo
                      checkSeq = threadedCheck options theChecker
                      saveProblem l s = Button {label = "Submit" , action = submitDer opts theChecker l g s}
                      options' = options { submit = case (M.lookup "submission" opts, M.lookup "goal" opts) of
                                                      (Just "saveRule",_) -> Just saveRule
                                                      (Just s, Just g) | take 7 s == "saveAs:" -> Just $ saveProblem (drop 7 s) (theSeq g)
                                                      _ -> Nothing
                                         }
                  checkerWith options' checkSeq iog w
                  
                  where options = optionsFromMap opts
                        saveRule = Button {label = "Save" , action = trySave drs}
                        theSeq g = case parse (ndParseSeq calc) "" g of
                                       Left e -> error "couldn't parse goal"
                                       Right seq -> seq

              parseGoal options calc = do let seqParse = ndParseSeq calc
                                              (Just seqstring) = M.lookup "goal" opts 
                                              --XXX: the directed option is set by the existence of a goal, so this match can't fail.
                                          case parse seqParse "" seqstring of
                                              Left e -> do setInnerHTML g (Just $ "Couldn't Parse This Goal:" ++ seqstring)
                                                           error "couldn't parse goal"
                                              Right seq -> do setInnerHTML g (Just $ alternateSymbols options $ show seq)
                                                              return $ Just seq
              makeDisplay = do (Just pd) <- createElement w (Just "div")
                               setAttribute pd "class" "proofDisplay"
                               (Just parent) <- getParentNode o
                               insertAdjacentElement (castToHTMLElement parent) "afterend" (Just pd)
                               return pd

              propChecker = Checker $ \self -> RuntimeNaturalDeductionConfig 
                                              <$> (M.fromList . map (\(x,y) -> (x,derivedRuleToSequent y)) <$> readIORef (checkerRules self))
                                              <*> (pure . toPremiseSeqs . sequent $ self)

              folChecker = Checker $ \self ->  RuntimeNaturalDeductionConfig 
                                              <$> (M.fromList .  map (\(x,y) -> (x, liftSequent . derivedRuleToSequent $ y)) <$> readIORef (checkerRules self))
                                              <*> (pure . toPremiseSeqs . sequent $ self)

              toPremiseSeqs :: (Concretes lex b, Typeable b) => Maybe (ClassicalSequentOver lex (Sequent b)) -> Maybe [ClassicalSequentOver lex (Sequent b)]
              toPremiseSeqs (Just seq) = Just . map (\x -> SA x :|-: SS x) $ toListOf (lhs . concretes) seq
              toPremiseSeqs Nothing = Nothing

              noRuntimeOptions = Checker $ const . pure $ RuntimeNaturalDeductionConfig mempty mempty

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
                                   do renderedProof <- renderer w ded
                                      setInnerHTML pd (Just "")
                                      appendChild pd (Just renderedProof)
                               Nothing -> return Nothing
                             Feedback mseq ds <- case ndProcessLineMemo ndcalc of
                                                     Just memoline -> toDisplaySequenceMemo (memoline $ proofMemo checker) ded
                                                     Nothing -> return $ toDisplaySequence (ndProcessLine ndcalc) ded
                             ul <- case feedback options of
                                       SyntaxOnly -> genericListToUl (syntaxwrap fd w) w ds
                                       _ -> genericListToUl (wrap fd w options) w ds
                             setInnerHTML fd (Just "")
                             appendChild fd (Just ul)
                             case sequent checker of
                                 Just s -> updateGoal s ref g mseq options
                                 Nothing -> computeRule ref g mseq options
           writeIORef (threadRef checker) (Just t')
           return ()

    where renderer = case ndRenderer (checkerCalc checker) of
                         MontagueStyle -> renderDeductionMontague
                         FitchStyle -> renderDeductionFitch
                         LemmonStyle v -> renderDeductionLemmon v

updateGoal s ref g mseq options = 
        case (mseq, feedback options) of
             (Nothing,_) -> setAttribute g "class" "goal" >> writeIORef ref False
             (Just seq, SyntaxOnly) -> setAttribute g "class" "goal" >> writeIORef ref (seq `seqSubsetUnify` s)
             (Just seq, _) -> if (seq `seqSubsetUnify` s) then do setAttribute g "class" "goal success"
                                                                  writeIORef ref True
                                                          else do setAttribute g "class" "goal failure"
                                                                  writeIORef ref False

computeRule ref g mseq options = 
        case mseq of
           Nothing -> do setInnerHTML g (Just "No Rule Found")
                         writeIORef ref False
           (Just seq) -> do setInnerHTML g (Just $ alternateSymbols options $ show seq)
                            writeIORef ref True

submitDer opts checker l g seq ref _ i = do isFinished <- liftIO $ readIORef ref
                                            (Just v) <- getValue (castToHTMLTextAreaElement i)
                                            liftIO $ if isFinished 
                                                then trySubmit Derivation opts l (DerivationDataOpts (pack $ show seq) (pack v) (M.toList opts)) True
                                                else do setAttribute g "class" "goal working"
                                                        rtconfig <- liftIO $ rulePost checker
                                                        let ndcalc = checkerCalc checker
                                                            ded = ndParseProof ndcalc rtconfig v
                                                        Feedback mseq _ <- case ndProcessLineMemo ndcalc of
                                                                               Just memoline -> toDisplaySequenceMemo (memoline $ proofMemo checker) ded
                                                                               Nothing -> return $ toDisplaySequence (ndProcessLine ndcalc) ded
                                                        setAttribute g "class" "goal"
                                                        case sequent checker of
                                                             Nothing -> message "No goal sequent to submit"
                                                             Just s -> case mseq of 
                                                                 (Just s') 
                                                                   | "exam" `elem` optlist -> trySubmit Derivation opts l (DerivationDataOpts (pack $ show seq) (pack v) (M.toList opts)) (s' `seqSubsetUnify` s)
                                                                   | otherwise -> if (s' `seqSubsetUnify` s) 
                                                                                   then trySubmit Derivation opts l (DerivationDataOpts (pack $ show seq) (pack v) (M.toList opts)) True
                                                                                   else message "not yet finished"
                                                                 _ | "exam" `elem` optlist -> trySubmit Derivation opts l (DerivationDataOpts (pack $ show seq) (pack v) (M.toList opts)) False
                                                                   | otherwise -> message "not yet finished"
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

trySave drs ref w i = do isFinished <- liftIO $ readIORef ref
                         rules <- liftIO $ readIORef drs
                         if isFinished
                           then do (Just v) <- getValue (castToHTMLTextAreaElement i)
                                   let Feedback mseq _ = toDisplaySequence (ndProcessLine montagueSCCalc) . ndParseProof montagueSCCalc (configFrom rules mempty) $ v
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

configFrom rules prems = RuntimeNaturalDeductionConfig (M.fromList . map (\(x,y) -> (x,derivedRuleToSequent y)) $ rules) prems

wrap fd w options elt (Right s) = popUpWith fd w elt "+" (alternateSymbols options $ show s) Nothing
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
wrap fd w options elt (Left (NoUnify eqs n)) = 
        popUpWith fd w elt "✗" ("Error on line " ++ show n ++ ". Can't match these premises with this conclusion, using this rule.") 
                               (Just $ alternateSymbols options $ toUniErr eqs)
wrap fd w _ elt (Left (NoResult _)) = setInnerHTML elt (Just "&nbsp;")

syntaxwrap fd w elt (Left (NoParse e n))       = popUpWith fd w elt "⚠" ("Can't read line " ++ show n ++ ". There may be a typo.") (Just . cleanIt . show $ e)
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
syntaxwrap fd w elt (Left (NoResult _))        = setInnerHTML elt (Just "&nbsp;")
syntaxwrap fd w elt _        = setInnerHTML elt (Just "-")

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
