{-# LANGUAGE FlexibleContexts #-}
module Carnap.GHCJS.Action.SequentCheck (sequentCheckAction) where

import Lib 
import Data.Tree
import Data.Map as M (lookup,Map, toList)
import Data.Either
import Data.Aeson
import Data.Text (pack)
import Data.Typeable (Typeable)
import Data.Aeson.Types
import Data.IORef (IORef, readIORef, newIORef, writeIORef)
import Data.Text.Encoding
import qualified Text.Parsec as P (parse) 
import Carnap.GHCJS.SharedTypes
import Control.Lens (view)
import Control.Concurrent
import Control.Monad.IO.Class (liftIO)
import GHCJS.DOM
import GHCJS.Types
import GHCJS.Marshal
import GHCJS.DOM.Types (Element, Document, IsElement)
import GHCJS.DOM.Element (setInnerHTML, click, setAttribute)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore, getParentElement)
import GHCJS.DOM.EventM
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Calculi.Util
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.Tableau.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
import Carnap.Languages.PurePropositional.Logic.Gentzen
import Carnap.Languages.PureFirstOrder.Logic.Gentzen
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.Util.ProofJS

sequentCheckAction ::  IO ()
sequentCheckAction = do
               initializeCallback "checkPropSequent" (checkSequent gentzenPropLKCalc Nothing)
               initializeCallback "checkFOLSequent" (checkSequent gentzenFOLKCalc Nothing)
               initializeCallback "checkIchikawaJenkinsSLTableau" (checkSequent ichikawaJenkinsSLTableauCalc Nothing)
               initializeCallback "checkSequentInfo" checkFullInfo
               initElements getCheckers activateChecker
               return ()

getCheckers :: IsElement self => Document -> self -> IO [Maybe (Element, Element, Map String String)]
getCheckers w = genInOutElts w "div" "div" "sequentchecker"

activateChecker :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateChecker _ Nothing  = return ()
activateChecker w (Just (i, o, opts))
        | sys == "propLK"  = setupWith gentzenPropLKCalc
        | sys == "propLJ"  = setupWith gentzenPropLJCalc
        | sys == "foLK"    = setupWith gentzenFOLKCalc
        | sys == "foLJ"    = setupWith gentzenFOLJCalc
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "propLK"

              setupWith calc = do
                  mseq <- parseGoal calc
                  let content = M.lookup "content" opts
                  root <- case (content >>= decodeJSON, mseq) of
                              (Just val,_) -> let Just c = content in initRoot c o
                              (_, Just seq) -> initRoot ("{\"label\": \"" ++ show seq
                                                          ++ "\", \"rule\":\"\", \"forest\": []}") o
                              _ -> initRoot "" o
                  threadRef <- newIORef (Nothing :: Maybe ThreadId)
                  bw <- createButtonWrapper w o
                  let submit = submitSeq w opts calc root
                  btStatus <- createSubmitButton w bw submit opts
                  initialCheck <- newListener $ liftIO $ do 
                                    t <- forkIO $ do
                                            threadDelay 500000
                                            mr <- toCleanVal root
                                            case mr of
                                                Just r -> checkSequent calc Nothing r >>= decorate root
                                                Nothing -> return ()
                                    writeIORef threadRef (Just t)
                                    updateGoal root i
                  addListener i initialize initialCheck False --initial check in case we preload a tableau
                  doOnce i mutate False $ liftIO $ btStatus Edited
                  case M.lookup "init" opts of Just "now" -> dispatchCustom w i "initialize"; _ -> return ()
                  root `onChange` (\_ -> dispatchCustom w i "mutate")
                  root `onChange` checkOnChange calc root i threadRef 

              parseGoal calc = do 
                  let seqParse = parseSeqOver $ tbParseForm calc
                  case M.lookup "goal" opts of
                      Just s -> case P.parse seqParse "" s of
                          Left e -> do setInnerHTML i (Just $ "Couldn't Parse This Goal:" ++ s)
                                       error "couldn't parse goal"
                          Right seq -> do setInnerHTML i (Just $ show seq) --will eventually want the equivalent of ndNotation
                                          return $ Just seq
                      Nothing -> return Nothing

submitSeq w opts calc root l = 
        do Just val <- liftIO $ toCleanVal root
           case parse parseTreeJSON val of
               Error s -> message "Something is wrong with the proof... Try again?"
               Success tree@(Node (content,_) _) -> case toTableau calc tree of
                     Left _ -> message "Something is wrong with the proof... Try again?"
                     Right tab -> case parse fromInfo . toInfo . validateTree $ tab of
                          Success rslt | "exam" `elem` optlist || rslt -> trySubmit w SequentCalc opts l (SequentCalcData (pack content) tree (toList opts)) rslt
                          _ -> message "Something is wrong with the proof... Try again?"
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

checkOnChange :: ( ReLex lex
                 , SupportsTableau rule lex sem 
                 ) => TableauCalc lex sem rule -> JSVal -> Element -> IORef (Maybe ThreadId) ->  JSVal -> IO ()
checkOnChange calc root i threadRef changed = do
        mt <- readIORef threadRef
        case mt of Just t -> killThread t
                   Nothing -> return ()
        t' <- forkIO $ do
            threadDelay 500000
            changedParent <- ascendTree changed --may need to update the parent of the changed node if it exists
            Just changedVal <- toCleanVal changed
            Just changedParentVal <- toCleanVal changedParent
            theParentInfo <- checkSequent calc (Just 1) changedParentVal 
            theInfo <- checkSequent calc (Just 1) changedVal 
            decorate changedParent theParentInfo
            decorate changed theInfo
            --XXX: we do these separately in order to keep a parse error in
            --either of the inferences from causing trouble in the
            --other inference.
            updateGoal root i
        writeIORef threadRef (Just t')

updateGoal :: JSVal -> Element -> IO ()
updateGoal root i = do Just wrap <- liftIO $ getParentElement i
                       Just info <- valToInfo root >>= fromJSVal 
                       case parse fromInfo info of
                           Success True -> setAttribute wrap "class" "success"
                           _ -> setAttribute wrap "class" "failure"

checkSequent :: ( ReLex lex
                , SupportsTableau rule lex sem 
                ) => TableauCalc lex sem rule -> Maybe Int -> Value -> IO Value
checkSequent calc depth v = case parse parseTreeJSON v of
                               Success t -> case toTableau calc (trimTree depth t) of 
                                   Left feedback -> return . toInfo . trimTree ((\x -> x - 1) <$> depth)  $ feedback
                                   Right tab -> return . toInfo . trimTree ((\x -> x - 1) <$> depth) . validateTree $ tab
                               Error s -> do print (show v)
                                             error s
    where trimTree (Just n) (Node s f) | n > 0 = Node s (map (trimTree (Just $ n - 1)) f)
                                       | otherwise = Node s []
          trimTree Nothing t = t

toTableau :: ( Typeable sem
             , ReLex lex
             , Sequentable lex
             ) => TableauCalc lex sem rule -> Tree (String,String) -> Either (TreeFeedback lex) (Tableau lex sem rule)
toTableau calc (Node (l,r) f) 
    | all isRight parsedForest && isRight newNode = Node <$> newNode <*> sequence parsedForest
    | isRight newNode = Left $ Node Waiting (map cleanTree parsedForest)
    | Left n <- newNode = Left n
    where parsedLabel = P.parse (parseSeqOver (tbParseForm calc)) "" l
          parsedRules = if r == "" then pure Nothing else P.parse (Just <$> tbParseRule calc) "" r
          parsedForest = map (toTableau calc) f
          cleanTree (Left fs) = fs
          cleanTree (Right fs) = fmap (const Waiting) fs
          newNode = case TableauNode <$> parsedLabel <*> (pure Nothing) <*> parsedRules of
                        Right n -> Right n
                        Left e -> Left (Node (ProofError $ NoParse e 0) (map cleanTree parsedForest))
