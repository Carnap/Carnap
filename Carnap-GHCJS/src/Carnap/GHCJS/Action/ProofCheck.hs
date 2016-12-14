{-#LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.ProofCheck (proofCheckAction) where

import Carnap.Calculi.NaturalDeduction.Checker (ProofErrorMessage(..), Feedback(..), seqSubsetUnify, hoToDisplaySequence, toDisplaySequence)
import Carnap.Core.Data.AbstractSyntaxDataTypes (liftLang)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Logic as P (DerivedRule(..), parsePropProof) 
import Carnap.Languages.PureFirstOrder.Logic as FOL (DerivedRule(..), parseFOLProof) 
import Carnap.Languages.PurePropositional.Util (toSchema)
import Carnap.GHCJS.SharedTypes
import Text.Parsec
import Data.IORef
import Data.Aeson as A
import qualified Data.Map as M (fromList,map) 
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
import Control.Monad.Trans.Maybe (runMaybeT, MaybeT(..))
import Control.Concurrent

proofCheckAction :: IO ()
proofCheckAction = do availableDerived <- newIORef []
                      print "starting"
                      genericSendJSON RequestDerivedRulesForUser (addRules availableDerived) errcb
                      initElements getCheckers (activateChecker availableDerived)

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
addRules avd v =  case fromJSON v :: Result String of
                    A.Error e -> do print $ "error decoding derived rules: " ++ e
                                    print $ "recieved string: " ++ show v
                    Success s -> do let v' = read s :: Value
                                    case fromJSON v' :: Result [(String,P.DerivedRule)] of
                                          A.Error e -> do print $ "error decoding derived rules: " ++ e
                                                          print $ "recieved JSON: " ++ show v
                                          Success rs -> do print $ show rs
                                                           writeIORef avd rs

getCheckers :: IsElement self => self -> IO [Maybe (Element, Element, Element, [String])]
getCheckers = getInOutGoalElts "proofchecker"

activateChecker ::  IORef [(String,P.DerivedRule)] -> Document -> Maybe (Element, Element, Element, [String]) -> IO ()
activateChecker _ _ Nothing  = return ()
activateChecker drs w (Just (i,o,g, classes))
        | "ruleMaker" `elem` classes = checkerWith "save rule" (trySave drs) (computeRule drs)
        | "firstOrder" `elem` classes = 
            do (Just gs) <- getInnerHTML g 
               case parse folSeqAndLabel "" (decodeHtml gs) of
                   Left e -> setInnerHTML g (Just "Couldn't Parse Goal")
                   Right (l,s) -> do mtref <- newIORef Nothing
                                     setInnerHTML g (Just $ show s)
                                     checkerWith "submit solution" (trySubmit l s) (folCheckSolution drs s mtref)
        | otherwise = 
            do (Just gs) <- getInnerHTML g 
               case parse seqAndLabel "" (decodeHtml gs) of
                   Left e -> setInnerHTML g (Just "Couldn't Parse Goal")
                   Right (l,s) -> do setInnerHTML g (Just $ show s)
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
wrap (Right seq)                = "<div>+<div><div>" ++ show seq ++ "<div></div></div>"

toUniErr eqs = "In order to apply this inference rule, there needs to be a substitution that makes at least one of these sets of pairings match:" 
                ++ (concat $ map endiv' $ map (concat . map (endiv . show) . reverse) eqs)
                -- TODO make this less horrible, give equations internal
                -- structure so that they can be aligned properly
    where endiv e = "<div>" ++ e ++ "</div>"
          endiv' e = "<div class=\"equations\">" ++ e ++ "</div>"

checkSolution drs s w ref v (g, fd)   =  do rules <- liftIO $ readIORef drs 
                                            -- XXX this is here, rather than earlier, 
                                            -- because if this ref is read too quickly, the async callback for the rules fails. 
                                            let Feedback mseq ds = toDisplaySequence (parsePropProof (M.fromList rules)) v
                                            updateGoal s w ref (g, fd) mseq ds

folCheckSolution drs s mtref w ref v (g, fd) = 
        do mt <- readIORef mtref
           rules <- liftIO $ readIORef drs 
           case mt of
               Just t -> killThread t
               Nothing -> return ()
           t' <- forkIO $ do threadDelay 200000
                             let Feedback mseq ds = hoToDisplaySequence (parseFOLProof $ M.map liftDerivedRule $ M.fromList rules) v
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
                                     let Feedback mseq ds = toDisplaySequence (parsePropProof (M.fromList rules)) v
                                     ul <- genericListToUl wrap w ds
                                     setInnerHTML fd (Just "")
                                     appendChild fd (Just ul)
                                     case mseq of
                                         Nothing -> do setInnerHTML g (Just "No Rule Found")
                                                       writeIORef ref False
                                         (Just seq) -> do setInnerHTML g (Just $ show seq)
                                                          writeIORef ref True
                                     return ()

errDiv msg lineno (Just details) = "<div>✗<div><div>Error on line " 
                                    ++ show lineno ++ ": " ++ msg 
                                    ++ "<div>see details<div>" 
                                    ++ details 
                                    ++ "</div></div></div></div></div>"
errDiv msg lineno Nothing = "<div>✗<div><div>Error on line " 
                              ++ show lineno ++ ": " ++ msg 
                              ++ "</div></div></div>"

-- XXX this should be a library function
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
                                     liftIO $ sendJSON 
                                        (SubmitDerivation (l ++ ":" ++ show s) v) 
                                        (loginCheck $ "Submitted Derivation for Exercise " ++ l)
                                        errorPopup
                             else alert w "not yet finished"

trySave drs ref w i = do isFinished <- liftIO $ readIORef ref
                         rules <- liftIO $ readIORef drs
                         if isFinished
                           then do (Just v) <- getValue (castToHTMLTextAreaElement i)
                                   let Feedback mseq _ = toDisplaySequence (parsePropProof (M.fromList rules)) v
                                   case mseq of
                                    Nothing -> alert w "A rule can't be extracted from this proof"
                                    (Just (a :|-: (SS c))) -> do
                                        -- XXX : throw a more transparent error here if necessary
                                        let prems = map (toSchema . fromSequent) (toListOf concretes a)
                                        let conc = (toSchema . fromSequent) c
                                        mname <- prompt w "What name will you give this rule (use all capital letters!)" (Just "")
                                        case mname of
                                            (Just name) -> if allcaps name 
                                                               then liftIO $ sendJSON (SaveDerivedRule name $ P.DerivedRule conc prems) loginCheck error
                                                               else alert w "rule name must be all capital letters"
                                            Nothing -> alert w "No name entered"
                           else alert w "not yet finished"
    where loginCheck c | c == "No User" = alert w "You need to log in before you can save a rule"
                       | c == "Clash"   = alert w "it appears you've already got a rule with this name"
                       | otherwise      = alert w "Saved your new rule!" >> reloadPage
          error c = alert w ("Something has gone wrong. Here's the error: " ++ c)
          allcaps s = and (map (`elem` "ABCDEFGHIJKLMNOPQRSTUVWXYZ") s)

-------------------------
--  Utility Functions  --
-------------------------

liftDerivedRule (P.DerivedRule conc prems) = FOL.DerivedRule (liftLang conc) (map liftLang prems)

