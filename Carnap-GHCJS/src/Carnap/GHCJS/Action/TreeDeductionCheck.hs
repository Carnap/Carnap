{-# LANGUAGE FlexibleContexts, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Action.TreeDeductionCheck (treeDeductionCheckAction) where

import Lib hiding (content)
import Data.Tree
import Data.Either
import Data.Map as M (lookup,Map, toList)
import Data.IORef (IORef, readIORef, newIORef, writeIORef)
import Data.Typeable (Typeable)
import Data.Aeson.Types
import Data.Text (pack)
import qualified Text.Parsec as P (parse) 
import Control.Monad.State (modify,get,execState,State)
import Control.Lens
import Control.Concurrent
import Control.Monad (mplus, (>=>))
import Control.Monad.IO.Class (liftIO)
import Carnap.Core.Unification.Unification (MonadVar,FirstOrder, applySub)
import Carnap.Core.Unification.ACUI (ACUI)
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Calculi.Tableau.Data
import Carnap.Languages.PurePropositional.Logic (ofPropTreeSys)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLTreeSys)
import Carnap.GHCJS.Util.ProofJS
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.HTMLElement (getInnerText, castToHTMLElement)
import GHCJS.DOM.Element (setInnerHTML, click, keyDown, input, setAttribute )
import GHCJS.DOM.Node (appendChild, removeChild, getParentNode, insertBefore, getParentElement)
import GHCJS.DOM.Types (Element, Document, IsElement)
import GHCJS.DOM.Document (createElement, getActiveElement)
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import GHCJS.DOM
import GHCJS.Types

treeDeductionCheckAction ::  IO ()
treeDeductionCheckAction = 
            do initializeCallback "checkProofTreeInfo" njCheck
               initElements getCheckers activateChecker
               return ()
    where njCheck = maybe (error "can't find PropNJ") id $ (\calc -> checkProofTree calc Nothing >=> return . fst) `ofPropTreeSys` "PropNJ" 

getCheckers :: IsElement self => Document -> self -> IO [Maybe (Element, Element, Map String String)]
getCheckers w = genInOutElts w "div" "div" "treedeductionchecker"

activateChecker :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateChecker _ Nothing  = return ()
activateChecker w (Just (i, o, opts)) = case (setupWith `ofPropTreeSys` sys) 
                                              `mplus` (setupWith `ofFOLTreeSys` sys)
                                        of Just io -> io
                                           Nothing -> error $ "couldn't parse tree system: " ++ sys
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "propNK"

              setupWith calc = do
                  mgoal <- parseGoal calc
                  let content = M.lookup "content" opts
                  root <- case (content >>= decodeJSON, mgoal) of
                              (Just val,_) -> let Just c = content in initRoot c o
                              (_, Just seq) | "prepopulate" `inOpts` opts -> 
                                                initRoot ("{\"label\": \"" ++ show (view rhs seq) 
                                                          ++ "\", \"rule\":\"\", \"forest\": []}") o
                              _ -> initRoot "{\"label\": \"\", \"rule\":\"\", \"forest\": []}" o
                  memo <- newIORef mempty
                  threadRef <- newIORef (Nothing :: Maybe ThreadId)
                  bw <- createButtonWrapper w o
                  let submit = submitTree w memo opts calc root mgoal
                  btStatus <- createSubmitButton w bw submit opts
                  if "displayJSON" `inOpts` opts 
                      then do
                          Just displayDiv <- createElement w (Just "div")
                          setAttribute displayDiv "class" "jsonDisplay"
                          setAttribute displayDiv "contenteditable" "true"
                          val <- toCleanVal root
                          setInnerHTML displayDiv . Just $ toJSONString val
                          toggleDisplay <- newListener $ do
                              kbe <- event
                              isCtrl <- getCtrlKey kbe
                              code <- liftIO $ keyString kbe
                              liftIO $ print code
                              if isCtrl && code == "?" 
                                  then do
                                      preventDefault
                                      mparent <- getParentNode displayDiv
                                      case mparent of
                                          Just p -> removeChild o (Just displayDiv)
                                          _ -> appendChild o (Just displayDiv)
                                      return ()
                                  else return ()
                          addListener o keyDown toggleDisplay False
                          updateRoot <- newListener $ liftIO $ do 
                                Just json <- getInnerText (castToHTMLElement displayDiv)
                                replaceRoot root json
                          addListener displayDiv input updateRoot False
                          root `onChange` (\_ -> do
                                   mfocus <- getActiveElement w
                                   --don't update when the display is
                                   --focussed, to avoid cursor jumping
                                   if Just displayDiv /= mfocus then do
                                       val <- toCleanVal root
                                       setInnerHTML displayDiv . Just $ toJSONString val
                                   else return ())
                          return ()
                      else return ()
                  initialCheck <- newListener $ liftIO $  do 
                                    forkIO $ do
                                        threadDelay 500000
                                        mr <- toCleanVal root
                                        case mr of
                                            Just r -> do (info,mseq) <- checkProofTree calc (Just memo) r 
                                                         decorate root info
                                                         Just wrap <- getParentElement i
                                                         updateInfo calc mgoal mseq wrap
                                            Nothing -> return ()
                                    return ()
                  addListener i initialize initialCheck False --initial check in case we preload a tableau
                  doOnce i mutate False $ liftIO $ btStatus Edited
                  case M.lookup "init" opts of Just "now" -> dispatchCustom w i "initialize"; _ -> return ()
                  root `onChange` (\_ -> dispatchCustom w i "mutate")
                  root `onChange` (\_ -> checkOnChange memo threadRef calc mgoal i root)

              parseGoal calc = do 
                  let seqParse = parseSeqOver $ tbParseForm calc
                  case M.lookup "goal" opts of
                      Just s -> case P.parse seqParse "" s of
                          Left e -> do setInnerHTML i (Just $ "Couldn't Parse This Goal:" ++ s)
                                       error "couldn't parse goal"
                          Right seq -> do setInnerHTML i (Just . tbNotation calc . show $ seq)
                                          return $ Just seq
                      Nothing -> do setInnerHTML i (Just "Awaiting a proof")
                                    return Nothing

updateInfo _ (Just goal) (Just seq) wrap | seq `seqSubsetUnify` goal = setAttribute wrap "class" "success"
updateInfo _ (Just goal) (Just seq) wrap = setAttribute wrap "class" "failure"
updateInfo calc Nothing (Just seq) wrap = setInnerHTML wrap (Just . tbNotation calc . show $ seq)
updateInfo _ Nothing Nothing wrap  = setInnerHTML wrap (Just "Awaiting a proof")
updateInfo _ _ _ wrap = setAttribute wrap "class" ""

submitTree w memo opts calc root (Just seq) l = 
        do Just val <- liftIO $ toCleanVal root
           case parse parseTreeJSON val of
               Error s -> message $ "Something has gone wrong. Here's the error:" ++ s
               Success tree -> case toProofTree calc tree of
                     Left _ | "exam" `inOpts` opts -> trySubmit w DeductionTree opts l (DeductionTreeData (pack (show seq)) tree (toList opts)) False
                     Left _ -> message "Something is wrong with the proof... Try again?"
                     Right prooftree -> do 
                          validation <- liftIO $ hoReduceProofTreeMemo memo (structuralRestriction prooftree) prooftree 
                          case validation of
                              Right seq' | "exam" `inOpts` opts || (seq' `seqSubsetUnify` seq) 
                                -> trySubmit w DeductionTree opts l (DeductionTreeData (pack (show seq)) tree (toList opts)) (seq' `seqSubsetUnify` seq)
                              _ -> message "Something is wrong with the proof... Try again?"

checkOnChange :: ( ReLex lex
                 , Sequentable lex
                 , Inference rule lex sem
                 , FirstOrder (ClassicalSequentOver lex)
                 , ACUI (ClassicalSequentOver lex)
                 , MonadVar (ClassicalSequentOver lex) (State Int)
                 , StaticVar (ClassicalSequentOver lex)
                 , Schematizable (lex (ClassicalSequentOver lex))
                 , CopulaSchema (ClassicalSequentOver lex)
                 , Typeable sem
                 , Show rule
                 , PrismSubstitutionalVariable lex
                 , FirstOrderLex (lex (ClassicalSequentOver lex))
                 , StructuralOverride rule (ProofTree rule lex sem)
                 , StructuralInference rule lex (ProofTree rule lex sem)
                 ) => ProofMemoRef lex sem rule -> IORef (Maybe ThreadId) -> TableauCalc lex sem rule 
                                                -> Maybe (ClassicalSequentOver lex (Sequent sem)) -> Element -> JSVal -> IO ()
checkOnChange memo threadRef calc mgoal i root = do
        mt <- readIORef threadRef
        case mt of Just t -> killThread t
                   Nothing -> return ()
        t' <- forkIO $ do
            threadDelay 500000
            Just changedVal <- toCleanVal root
            (theInfo, mseq) <- checkProofTree calc (Just memo) changedVal 
            decorate root theInfo
            Just wrap <- getParentElement i
            updateInfo calc mgoal mseq wrap
        writeIORef threadRef (Just t')

toProofTree :: ( Typeable sem
               , ReLex lex
               , Sequentable lex
               , StructuralOverride rule (ProofTree rule lex sem)
               , Inference rule lex sem
               ) => TableauCalc lex sem rule -> Tree (String,String) -> Either (TreeFeedback lex) (ProofTree rule lex sem)
toProofTree calc (Node (l,r) f) 
    | all isRight parsedForest && isRight newNode = handleOverride <$> (Node <$> newNode <*> sequence parsedForest)
    | isRight newNode = Left $ Node Waiting (map cleanTree parsedForest)
    | Left n <- newNode = Left n
    where parsedLabel = (SS . liftToSequent) <$> P.parse (tbParseForm calc) "" l
          parsedRules = P.parse (tbParseRule calc) "" r
          parsedForest = map (toProofTree calc) f
          cleanTree (Left fs) = fs
          cleanTree (Right fs) = fmap (const Waiting) fs
          newNode = case ProofLine 0 <$> parsedLabel <*> parsedRules of
                        Right l -> Right l
                        Left e -> Left (Node (ProofError $ NoParse e 0) (map cleanTree parsedForest))
          handleOverride f@(Node l fs) = case structuralOverride f (head (rule l)) of
                                               Nothing -> f
                                               Just rs -> Node (l {rule = rs}) fs

checkProofTree :: ( ReLex lex
                  , Sequentable lex
                  , Inference rule lex sem
                  , FirstOrder (ClassicalSequentOver lex)
                  , ACUI (ClassicalSequentOver lex)
                  , MonadVar (ClassicalSequentOver lex) (State Int)
                  , StaticVar (ClassicalSequentOver lex)
                  , Schematizable (lex (ClassicalSequentOver lex))
                  , CopulaSchema (ClassicalSequentOver lex)
                  , Typeable sem
                  , Show rule
                  , StructuralOverride rule (ProofTree rule lex sem)
                  , StructuralInference rule lex (ProofTree rule lex sem)
                  ) => TableauCalc lex sem rule -> Maybe (ProofMemoRef lex sem rule) -> Value -> IO (Value, Maybe (ClassicalSequentOver lex (Sequent sem)))
checkProofTree calc mmemo v = case parse parseTreeJSON v of
                           Success t -> case toProofTree calc t of 
                                  Left feedback -> return (toInfo feedback, Nothing)
                                  Right tree -> do (val,mseq) <- validateProofTree calc mmemo tree
                                                   return (toInfo val, mseq)
                           Error s -> do print (show v)
                                         error s

validateProofTree :: ( ReLex lex
                     , Sequentable lex
                     , Inference rule lex sem
                     , FirstOrder (ClassicalSequentOver lex)
                     , ACUI (ClassicalSequentOver lex)
                     , MonadVar (ClassicalSequentOver lex) (State Int)
                     , StaticVar (ClassicalSequentOver lex)
                     , Schematizable (lex (ClassicalSequentOver lex))
                     , CopulaSchema (ClassicalSequentOver lex)
                     , Typeable sem
                     , Show rule
                     , StructuralInference rule lex (ProofTree rule lex sem)
                     ) => TableauCalc lex sem rule -> Maybe (ProofMemoRef lex sem rule) 
                       -> ProofTree rule lex sem -> IO (TreeFeedback lex, Maybe (ClassicalSequentOver lex (Sequent sem)))
validateProofTree calc mmemo t@(Node _ fs) = do rslt <- case mmemo of 
                                                     Nothing -> return $ hoReduceProofTree (structuralRestriction t) t
                                                     Just memo -> hoReduceProofTreeMemo memo (structuralRestriction t) t
                                                case rslt of
                                                     Left msg -> (,) <$> (Node <$> pure (ProofError msg) <*> mapM (validateProofTree calc mmemo >=> return . fst) fs) 
                                                                     <*> pure Nothing
                                                     Right seq ->  (,) <$> (Node <$> pure (ProofData (tbNotation calc . show $ seq)) <*> mapM (validateProofTree calc mmemo >=> return . fst) fs) 
                                                                    <*> pure (Just seq)
