{-# LANGUAGE FlexibleContexts, OverloadedStrings, CPP, JavaScriptFFI #-}
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
import Carnap.GHCJS.Util.ProofJS
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.Element (setInnerHTML, click)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.Types (Element, Document, IsElement)
import GHCJS.DOM.EventM
import GHCJS.DOM
import GHCJS.Types

treeDeductionCheckAction ::  IO ()
treeDeductionCheckAction = 
            do initializeCallback "checkProofTreeInfo" njCheck
               initElements getCheckers activateChecker
               return ()
    where njCheck = maybe (error "can't find PropNJ") id $ (\calc -> checkProofTree calc Nothing) `ofPropTreeSys` "PropNJ" 

getCheckers :: IsElement self => Document -> self -> IO [Maybe (Element, Element, Map String String)]
getCheckers w = genInOutElts w "div" "div" "treedeductionchecker"

activateChecker :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateChecker _ Nothing  = return ()
activateChecker w (Just (i, o, opts)) = case setupWith `ofPropTreeSys` sys of
                                            Just io -> io
                                            Nothing -> error $ "couldn't parse tree system: " ++ sys
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "propNK"

              setupWith calc = do
                  mseq <- parseGoal calc
                  let content = M.lookup "content" opts
                  root <- case (content >>= decodeJSON, mseq) of
                              (Just val,_) -> let Just c = content in initRoot c o
                              (_, Just seq) -> initRoot ("{\"label\": \"" ++ show (view rhs seq) 
                                                          ++ "\", \"rule\":\"\", \"forest\": []}") o
                              _ -> initRoot "" o
                  memo <- newIORef mempty
                  threadRef <- newIORef (Nothing :: Maybe ThreadId)
                  bw <- createButtonWrapper w o
                  let submit = submitTree memo opts calc root mseq
                  btStatus <- createSubmitButton w bw submit opts
                  initialCheck <- newListener $ liftIO $  do 
                                    forkIO $ do
                                        threadDelay 500000
                                        mr <- toCleanVal root
                                        case mr of
                                            Just r -> checkProofTree calc (Just memo) r >>= decorate root
                                            Nothing -> return ()
                                    return ()
                  addListener i initialize initialCheck False --initial check in case we preload a tableau
                  doOnce i mutate False $ liftIO $ btStatus Edited
                  case M.lookup "init" opts of Just "now" -> dispatchCustom w i "initialize"; _ -> return ()
                  root `onChange` (\_ -> dispatchCustom w i "mutate")
                  root `onChange` (\_ -> checkOnChange memo threadRef calc root)

              parseGoal calc = do 
                  let seqParse = parseSeqOver $ tbParseForm calc
                  case M.lookup "goal" opts of
                      Just s -> case P.parse seqParse "" s of
                          Left e -> do setInnerHTML i (Just $ "Couldn't Parse This Goal:" ++ s)
                                       error "couldn't parse goal"
                          Right seq -> do setInnerHTML i (Just $ show seq) --TODO: will eventually want the equivalent of ndNotation
                                          return $ Just seq
                      Nothing -> return Nothing

submitTree memo opts calc root (Just seq) l = 
        do Just val <- liftIO $ toCleanVal root
           case parse parseTreeJSON val of
               Error s -> message $ "Something has gone wrong. Here's the error:" ++ s
               Success tree -> case toProofTree calc tree of
                     Left _ | "exam" `elem` optlist -> trySubmit DeductionTree opts l (DeductionTreeData (pack (show seq)) tree (toList opts)) False
                     Left _ -> message "Something is wrong with the proof... Try again?"
                     Right prooftree -> do 
                          validation <- liftIO $ hoReduceProofTreeMemo memo (structuralRestriction prooftree) prooftree 
                          case validation of
                              Right seq' | "exam" `elem` optlist || (seq' `seqSubsetUnify` seq) 
                                -> trySubmit DeductionTree opts l (DeductionTreeData (pack (show seq)) tree (toList opts)) (seq' `seqSubsetUnify` seq)
                              _ -> message "Something is wrong with the proof... Try again?"
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

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
                 , StructuralInference rule lex (ProofTree rule lex sem)
                 ) => ProofMemoRef lex sem rule -> IORef (Maybe ThreadId) -> TableauCalc lex sem rule -> JSVal -> IO ()
checkOnChange memo threadRef calc root = do
        mt <- readIORef threadRef
        case mt of Just t -> killThread t
                   Nothing -> return ()
        t' <- forkIO $ do
            threadDelay 500000
            Just changedVal <- toCleanVal root
            theInfo <- checkProofTree calc (Just memo) changedVal 
            decorate root theInfo
            return ()
        writeIORef threadRef (Just t')

toProofTree :: ( Typeable sem
               , ReLex lex
               , Sequentable lex
               , Inference rule lex sem
               ) => TableauCalc lex sem rule -> Tree (String,String) -> Either (TreeFeedback lex) (ProofTree rule lex sem)
toProofTree calc (Node (l,r) f) 
    | all isRight parsedForest && isRight newNode = Node <$> newNode <*> sequence parsedForest
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
                  , StructuralInference rule lex (ProofTree rule lex sem)
                  ) => TableauCalc lex sem rule -> Maybe (ProofMemoRef lex sem rule) -> Value -> IO Value
checkProofTree calc mmemo v = case parse parseTreeJSON v of
                           Success t -> case toProofTree calc t of 
                                  Left feedback -> return . toInfo $ feedback
                                  Right tree -> toInfo <$> validateProofTree mmemo tree
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
                     ) => Maybe (ProofMemoRef lex sem rule) -> ProofTree rule lex sem -> IO (TreeFeedback lex)
validateProofTree mmemo t@(Node _ fs) = do rslt <- case mmemo of Nothing -> return $ hoReduceProofTree (structuralRestriction t) t
                                                                 Just memo -> hoReduceProofTreeMemo memo (structuralRestriction t) t
                                           case rslt of
                                              Left msg -> Node <$> pure (ProofError msg) <*> mapM (validateProofTree mmemo) fs
                                              Right seq ->  Node <$> pure (ProofData (show seq)) <*> mapM (validateProofTree mmemo) fs
