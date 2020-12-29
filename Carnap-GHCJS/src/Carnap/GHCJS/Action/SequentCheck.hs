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
import Control.Monad (mplus)
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
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PureFirstOrder.Logic
import Carnap.Languages.PureFirstOrder.Logic.Gentzen
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.Util.ProofJS

sequentCheckAction ::  IO ()
sequentCheckAction = do
               ---TODO: rewrite to use of____SeqSys, rather than doing this ad hoc.
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
activateChecker w (Just (i, o, opts))= maybe noSystem id ((setupWith `ofPropSeqSys` sys) 
                                                  `mplus` (setupWith `ofFOLSeqSys` sys))
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "propLK"

              noSystem = do setInnerHTML o (Just $ "Can't find a sequent calculus system named " ++ sys)
                            error $ "couldn't find formal system:" ++ sys

              setupWith calc = do
                  mseq <- parseGoal calc
                  let content = M.lookup "content" opts
                  root <- case (content >>= decodeJSON, mseq) of
                              (Just val,Just seq) -> let Just c = content in initRoot c o
                              (Just val,Nothing) -> let Just c = content in initMutRoot c o
                              (_, Just seq) -> initRoot ("{\"label\": \"" ++ (tbNotation calc . show $ seq)
                                                          ++ "\", \"rule\":\"\", \"forest\": []}") o
                              _ -> initMutRoot "{\"label\": \"⊢\", \"rule\":\"\", \"forest\": []}" o
                  initialLabel <- getRootLabel root
                  let hasGoal = not (null mseq)
                  threadRef <- newIORef (Nothing :: Maybe ThreadId)
                  bw <- createButtonWrapper w o
                  let submit = submitSeq w opts calc root initialLabel
                  btStatus <- createSubmitButton w bw submit opts
                  if "displayJSON" `inOpts` opts then attachDisplay w o root else return ()
                  initialCheck <- newListener $ liftIO $ do 
                                    t <- forkIO $ do
                                            threadDelay 500000
                                            renewRoot root calc
                                            if hasGoal then updateGoal w calc root initialLabel i --TODO: should check against seq rather than initialValue
                                                       else calculateResult calc root i
                                    writeIORef threadRef (Just t)
                  addListener i initialize initialCheck False --initial check in case we preload a tableau
                  case M.lookup "init" opts of Just "now" -> dispatchCustom w i "initialize"; _ -> return ()
                  doOnce i mutate False $ liftIO $ btStatus Edited
                  root `onChange` (\_ -> dispatchCustom w i "mutate")
                  root `onChange` checkOnChange w calc root hasGoal initialLabel i threadRef 

              parseGoal calc = do 
                  let seqParse = parseSeqOver $ tbParseForm calc
                  case M.lookup "goal" opts of
                      Just s -> case P.parse seqParse "" s of
                          Left e -> do setInnerHTML i (Just $ "Couldn't Parse This Goal:" ++ s)
                                       error "couldn't parse goal"
                          Right seq -> do setInnerHTML i (Just . tbNotation calc . show $ seq) --will eventually want the equivalent of ndNotation
                                          return $ Just seq
                      Nothing -> return Nothing

submitSeq w opts calc root initialLabel l = 
        do Just val <- liftIO $ toCleanVal root
           currentLabel <- liftIO $ getRootLabel root
           case parse parseTreeJSON val of
               Error s -> message "Something is wrong with the proof... Try again?"
               Success tree@(Node (content,_) _) -> case toTableau calc tree of
                     Left _ -> message "Something is wrong with the proof... Try again?"
                     Right tab -> case parse fromInfo . toInfo . validateTree $ tab of
                          Success rslt | initialLabel /= currentLabel -> message "The endsequent doesn't match the goal... Try again?"
                          Success (Just rslt) | "exam" `elem` optlist || rslt -> trySubmit w SequentCalc opts l (SequentCalcData (pack content) tree (toList opts)) rslt
                          _ -> message "Something is wrong with the proof... Try again?"
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

checkOnChange :: ( ReLex lex
                 , SupportsTableau rule lex sem 
                 ) => Document -> TableauCalc lex sem rule -> JSVal -> Bool -> String -> Element -> IORef (Maybe ThreadId) ->  JSVal -> IO ()
checkOnChange w calc root hasGoal initialLabel i threadRef changed = do
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
            --XXX: we do these separately in order to keep a parse error in
            --either of the inferences from causing trouble in the
            --other inference.
            decorate changedParent theParentInfo
            if isEmptyLeaf changedVal then decorate changed blankInfo --blank out the info of empty leaves
                                      else decorate changed theInfo
            if hasGoal then updateGoal w calc root initialLabel i 
                       else calculateResult calc root i
        writeIORef threadRef (Just t')

updateGoal :: (ReLex lex
              , SupportsTableau rule lex sem
              ) => Document -> TableauCalc lex sem rule -> JSVal -> String -> Element -> IO ()
updateGoal w calc root initialLabel i = 
        do Just wrap <- liftIO $ getParentElement i
           Just info <- valToInfo root >>= fromJSVal 
           currentLabel <- getRootLabel root
           case parse fromInfo info of
               Success (Just True) | currentLabel == initialLabel -> setSuccess w wrap
               --the equality check here is a precation against cheating by DOM manipulation
               Success Nothing -> do print "detected global edit"
                                     renewRoot root calc
                                     Just newinfo <- valToInfo root >>= fromJSVal 
                                     case parse fromInfo newinfo of
                                         Success (Just True) -> setSuccess w wrap 
                                         Success Nothing -> setInnerHTML i $ Just "Error: didn't handle global edit"
                                         _ -> setFailure w wrap
               _ -> setFailure w wrap

calculateResult :: (ReLex lex
                   , SupportsTableau rule lex sem
                   ) => TableauCalc lex sem rule -> JSVal -> Element -> IO ()
calculateResult calc root i = 
        do Just wrap <- liftIO $ getParentElement i
           Just info <- valToInfo root >>= fromJSVal 
           currentLabel <- getRootLabel root
           case parse fromInfo info of
               Success (Just True) -> displayLabel currentLabel
               Success Nothing -> do print "detected global edit"
                                     renewRoot root calc
                                     Just newinfo <- valToInfo root >>= fromJSVal 
                                     case parse fromInfo newinfo of
                                         Success (Just True) -> displayLabel currentLabel
                                         Success Nothing -> setInnerHTML i $ Just "Error: didn't handle global edit"
                                         _ -> wrong
               _ -> wrong
    where seqParse = parseSeqOver $ tbParseForm calc
          wrong = setInnerHTML i $ Just "No proven endsequent detected"
          displayLabel lbl = case P.parse seqParse "" lbl of
                               Left e -> do setInnerHTML i $ Just $ "Parse Error:" ++ show e
                               Right seq -> do setInnerHTML i (Just . tbNotation calc . show $ seq)

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

renewRoot root calc = do
    mr <- toCleanVal root
    case mr of
        Just r -> checkSequent calc Nothing r >>= decorate root
        Nothing -> print "couldn't clean root"
