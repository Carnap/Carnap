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
import Carnap.Languages.PurePropositional.Logic.Gentzen
import Carnap.GHCJS.Util.ProofJS
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.Element (setInnerHTML, click)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.Types (Element, Document, IsElement)
import GHCJS.DOM.EventM
import GHCJS.DOM
import GHCJS.Types

treeDeductionCheckAction ::  IO ()
treeDeductionCheckAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initializeCallback "checkProofTreeInfo" (checkProofTree gentzenPropNJCalc)
               initElements getCheckers activateChecker
               return ()

getCheckers :: IsElement self => Document -> self -> IO [Maybe (Element, Element, Map String String)]
getCheckers w = genInOutElts w "div" "div" "treedeductionchecker"

activateChecker :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateChecker _ Nothing  = return ()
activateChecker w (Just (i, o, opts))
        | sys == "propNK"  = setupWith gentzenPropNKCalc
        | sys == "propNJ"  = setupWith gentzenPropNJCalc
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
                  threadRef <- newIORef (Nothing :: Maybe ThreadId)
                  case M.lookup "submission" opts of
                     Just s | take 7 s == "saveAs:" -> do
                         bw <- buttonWrapper w
                         let l = Prelude.drop 7 s
                         bt <- doneButton w "Submit Solution"
                         appendChild bw (Just bt)
                         submit <- newListener $ liftIO $ submitTree opts l calc root
                         addListener bt click submit False                
                         mpar@(Just par) <- getParentNode o               
                         appendChild par (Just bw)
                         return ()
                     _ -> return ()
                  initialCheck <- newListener $ liftIO $  do 
                                    forkIO $ do
                                        threadDelay 500000
                                        mr <- toCleanVal root
                                        case mr of
                                            Just r -> checkProofTree calc r >>= decorate root
                                            Nothing -> return ()
                                    return ()
                  addListener i initialize initialCheck False --initial check in case we preload a tableau
                  root `onChange` (\_ -> checkOnChange threadRef calc root)

              parseGoal calc = do 
                  let seqParse = parseSeqOver $ tbParseForm calc
                  case M.lookup "goal" opts of
                      Just s -> case P.parse seqParse "" s of
                          Left e -> do setInnerHTML i (Just $ "Couldn't Parse This Goal:" ++ s)
                                       error "couldn't parse goal"
                          Right seq -> do setInnerHTML i (Just $ show seq) --TODO: will eventually want the equivalent of ndNotation
                                          return $ Just seq
                      Nothing -> return Nothing

submitTree opts l calc root = 
        do Just val <- toCleanVal root
           case parse parseTreeJSON val of
               Error s -> message "Something is wrong with the proof... Try again?"
               Success tree@(Node (content,_) _) -> case toProofTree calc tree of
                     Left _ -> message "Something is wrong with the proof... Try again?"
                     Right prooftree -> case parse fromInfo . toInfo . validateProofTree $ prooftree of
                          Success rslt | "exam" `elem` optlist || rslt -> trySubmit DeductionTree opts l (DeductionTreeData (pack content) tree (toList opts)) rslt
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
                 , StructuralInference rule lex (ProofTree rule lex sem)
                 ) => IORef (Maybe ThreadId) -> TableauCalc lex sem rule -> JSVal -> IO ()
checkOnChange threadRef calc root = do
        mt <- readIORef threadRef
        case mt of Just t -> killThread t
                   Nothing -> return ()
        t' <- forkIO $ do
            threadDelay 500000
            Just changedVal <- toCleanVal root
            theInfo <- checkProofTree calc changedVal 
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
                  , StructuralInference rule lex (ProofTree rule lex sem)
                  ) => TableauCalc lex sem rule -> Value -> IO Value
checkProofTree calc v = case parse parseTreeJSON v of
                           Success t -> case toProofTree calc t of 
                                  Left feedback -> return . toInfo $ feedback
                                  Right tree -> return . toInfo $ validateProofTree $ tree
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
                     , StructuralInference rule lex (ProofTree rule lex sem)
                     ) => ProofTree rule lex sem -> TreeFeedback lex
validateProofTree t@(Node _ fs) = case hoReduceProofTree (structuralRestriction t) t of
              Left msg -> Node (ProofError msg) (map validateProofTree fs)
              Right seq -> Node (ProofData (show seq)) (map validateProofTree fs)
