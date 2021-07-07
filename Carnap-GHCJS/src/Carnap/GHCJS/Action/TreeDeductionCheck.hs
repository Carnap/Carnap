{-# LANGUAGE FlexibleContexts, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Action.TreeDeductionCheck (treeDeductionCheckAction) where

import Lib hiding (content)
import Data.Tree
import Data.Either
import Data.Map as M (lookup, Map, toList, fromList, filterWithKey)
import Data.IORef (IORef, readIORef, newIORef, writeIORef)
import Data.Typeable (Typeable)
import Data.Aeson.Types
import Data.Char (toLower)
import Data.Text (pack)
import qualified Text.Parsec as P
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
import Carnap.Languages.SetTheory.Logic (ofSetTheoryTreeSys)
import Carnap.Languages.Arithmetic.Parser (arithmeticExtendedSchemaParser)
import Carnap.Languages.Arithmetic.Logic (ofArithmeticTreeSys)
import Carnap.Languages.HigherOrderArithmetic.Logic (ofHigherOrderArithmeticTreeSys)
import Carnap.GHCJS.Util.ProofJS
import Carnap.GHCJS.SharedTypes
import GHCJS.DOM.HTMLElement (setInnerText, castToHTMLElement)
import GHCJS.DOM.Element (click, keyDown, setAttribute )
import GHCJS.DOM.Node (getParentElement)
import GHCJS.DOM.Types (Element, Document, IsElement)
import GHCJS.DOM.EventM
import GHCJS.DOM
import GHCJS.Types

data CheckerParameters rule lex sem = CheckerParameters 
            { tableauCalc :: TableauCalc lex sem rule
            , threadRef :: IORef (Maybe ThreadId)
            , proofMemo :: ProofMemoRef lex sem rule
            --We include an argument here in case we want to pack some
            --IORefs into the CheckerParameters, and want the RuntimeConfig
            --to have access to those
            , runtimeConfig' :: CheckerParameters rule lex sem -> IO (RuntimeDeductionConfig lex sem)
            }

runtimeConfig x = runtimeConfig' x x 

treeDeductionCheckAction ::  IO ()
treeDeductionCheckAction = 
            do njCheck <- mkNJCheck
               initializeCallback "checkProofTreeInfo" njCheck
               initElements getCheckers activateChecker
               return ()
    where mkNJCheck = do 
           case (\calc -> newCheckerBuilder calc ) `ofPropTreeSys` "PropNJ" of
               Nothing -> return $ error "can't find PropNJ"
               Just checkerBuilder -> do checker <- checkerBuilder
                                         return (checker >=> return . fst)
          newCheckerBuilder calc = do
              memo <- newIORef mempty
              ref <- newIORef (Nothing :: Maybe ThreadId)
              return (checkProofTree (CheckerParameters 
                             { threadRef = ref
                             , proofMemo = memo
                             , tableauCalc = calc
                             , runtimeConfig' = \_ -> return (defaultRuntimeDeductionConfig)
                             }))

getCheckers :: IsElement self => Document -> self -> IO [Maybe (Element, Element, Map String String)]
getCheckers w = genInOutElts w "div" "div" "treedeductionchecker"

activateChecker :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateChecker _ Nothing  = return ()
activateChecker w (Just (i, o, opts)) = case (setupWith defaultRTC `ofPropTreeSys` sys) 
                                              `mplus` (setupWith defaultRTC `ofFOLTreeSys` sys)
                                              `mplus` (setupWith axiomsRTC `ofSetTheoryTreeSys` sys)
                                              `mplus` (setupWith axiomsRTC `ofArithmeticTreeSys` sys)
                                              `mplus` (setupWith defaultRTC `ofHigherOrderArithmeticTreeSys` sys)
                                        of Just io -> io
                                           Nothing -> error $ "couldn't parse tree system: " ++ sys
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "propNK"

              defaultRTC calc _ = return (defaultRuntimeDeductionConfig)
              axiomsRTC calc _ = case tbParseAxiomScheme calc of
                                        Nothing -> return defaultRuntimeDeductionConfig
                                        Just axParse -> do
                                           let axOpts = M.toList $ M.filterWithKey (\k _ -> take 6 k == "axiom-") opts
                                               axPairs = map (\(k,v) -> (map toLower . drop 6 $ k, v) ) axOpts
                                               parseAxioms = P.sepBy1 (parseSeqOver axParse) (P.char ';') <* P.eof
                                               axRslts = mapM (\(k,v) -> (,) <$> return k <*> P.parse parseAxioms "" v) axPairs
                                           case axRslts of
                                               Right rslts -> return $ defaultRuntimeDeductionConfig { runtimeAxioms = M.fromList rslts }
                                               Left e -> do errorPopup $ "couldn't parse axioms: " ++ show e
                                                            return defaultRuntimeDeductionConfig

              setupWith rtc calc = do
                  mgoal <- parseGoal calc
                  let content = M.lookup "content" opts
                  root <- case (content >>= decodeJSON, mgoal) of
                              (Just val,_) -> let Just c = content in initMutRoot c o
                              (_, Just seq) | "prepopulate" `inOpts` opts -> 
                                                initMutRoot ("{\"label\": \"" ++ show (view rhs seq) 
                                                          ++ "\", \"rule\":\"\", \"forest\": []}") o
                              _ -> initMutRoot "{\"label\": \"\", \"rule\":\"\", \"forest\": []}" o
                  memo <- newIORef mempty
                  theThreadRef <- newIORef (Nothing :: Maybe ThreadId)
                  bw <- createButtonWrapper w o
                  let checkerParams = CheckerParameters 
                        { tableauCalc = calc
                        , threadRef = theThreadRef
                        , proofMemo = memo
                        , runtimeConfig' = rtc calc
                        }
                  let submit = submitTree w checkerParams opts root mgoal
                  btStatus <- createSubmitButton w bw submit opts
                  if "displayJSON" `inOpts` opts then attachDisplay w o root else return ()
                  initialCheck <- newListener $ liftIO $ do 
                                    forkIO $ do
                                        threadDelay 500000
                                        mr <- toCleanVal root
                                        case mr of
                                            Just r -> do (info,mseq) <- checkProofTree checkerParams r 
                                                         decorate root info
                                                         updateInfo w calc mgoal mseq i
                                            Nothing -> return ()
                                    return ()
                  addListener i initialize initialCheck False --initial check in case we preload a tableau
                  doOnce i mutate False $ liftIO $ btStatus Edited
                  case M.lookup "init" opts of Just "now" -> dispatchCustom w i "initialize"; _ -> return ()
                  root `onChange` (\_ -> dispatchCustom w i "mutate")
                  root `onChange` (\_ -> checkOnChange w checkerParams mgoal i root)

              parseGoal calc = do 
                  let seqParse = parseSeqOver (tbParseForm calc)
                  case M.lookup "goal" opts of
                      Just s -> case P.parse (seqParse <* P.eof) "" s of
                          Left e -> do setInnerText (castToHTMLElement i) (Just $ "Couldn't Parse This Goal:" ++ s)
                                       error "couldn't parse goal"
                          Right seq -> do setInnerText (castToHTMLElement i) (Just . tbNotation calc . show $ seq)
                                          return $ Just seq
                      Nothing -> do setInnerText (castToHTMLElement i) (Just "Awaiting a proof")
                                    return Nothing

updateInfo w _ (Just goal) (Just seq) i = 
        do Just wrap <- getParentElement i
           if seq `seqSubsetUnify` goal 
               then setSuccess w wrap 
               else setFailure w wrap
updateInfo _ calc Nothing (Just seq) i = setInnerText (castToHTMLElement i) (Just . tbNotation calc . show $ seq)
updateInfo _ _ Nothing Nothing i = setInnerText (castToHTMLElement i) (Just "Awaiting a proof")
updateInfo w _ _ _ i = do wrap <- getParentElement i
                          maybe (return ()) (\w -> setAttribute w "class" "") wrap

submitTree w checkerParams opts root (Just seq) l = 
        do Just val <- liftIO $ toCleanVal root
           rtc <- liftIO $ runtimeConfig checkerParams
           case parse parseTreeJSON val of
               Error s -> message $ "Something has gone wrong. Here's the error:" ++ s
               Success tree -> case toProofTree rtc checkerParams tree of
                     Left _ | "exam" `inOpts` opts -> trySubmit w DeductionTree opts l (DeductionTreeData (pack (show seq)) tree (toList opts)) False
                     Left _ -> message "Something is wrong with the proof... Try again?"
                     Right prooftree -> do 
                          validation <- liftIO $ hoReduceProofTreeMemo (proofMemo checkerParams) (structuralRestriction prooftree) prooftree 
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
                 ) => Document -> CheckerParameters rule lex sem -> Maybe (ClassicalSequentOver lex (Sequent sem)) -> Element -> JSVal -> IO ()
checkOnChange w checkerParameters mgoal i root = do
        mt <- readIORef (threadRef checkerParameters)
        case mt of Just t -> killThread t
                   Nothing -> return ()
        t' <- forkIO $ do
            threadDelay 500000
            Just changedVal <- toCleanVal root
            (theInfo, mseq) <- checkProofTree checkerParameters changedVal 
            decorate root theInfo
            updateInfo w (tableauCalc checkerParameters) mgoal mseq i
        writeIORef (threadRef checkerParameters) (Just t')

toProofTree :: ( Typeable sem
               , ReLex lex
               , Sequentable lex
               , StructuralOverride rule (ProofTree rule lex sem)
               , Inference rule lex sem
               ) => RuntimeDeductionConfig lex sem -> CheckerParameters rule lex sem -> Tree (String,String) -> Either (TreeFeedback lex) (ProofTree rule lex sem)
toProofTree rtc checkerParams (Node (l,r) f) 
    | all isRight parsedForest && isRight newNode = handleOverride <$> (Node <$> newNode <*> sequence parsedForest)
    | isRight newNode = Left $ Node Waiting (map cleanTree parsedForest)
    | Left n <- newNode = Left n
    where parsedLabel = (SS . liftToSequent) <$> P.parse (P.spaces *> tbParseForm (tableauCalc checkerParams) <* P.eof) "" l
          parsedRules = P.parse (tbParseRule (tableauCalc checkerParams) rtc) "" r
          parsedForest = map (toProofTree rtc checkerParams) f
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
                  ) => CheckerParameters rule lex sem -> Value -> IO (Value, Maybe (ClassicalSequentOver lex (Sequent sem)))
checkProofTree checkerParams v = do
        rtc <- runtimeConfig checkerParams
        case parse parseTreeJSON v of
           Success t -> case toProofTree rtc checkerParams t of 
                  Left feedback -> return (toInfo feedback, Nothing)
                  Right tree -> do (val,mseq) <- validateProofTree checkerParams tree
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
                     ) => CheckerParameters rule lex sem -> ProofTree rule lex sem -> IO (TreeFeedback lex, Maybe (ClassicalSequentOver lex (Sequent sem)))
validateProofTree checkerParams t@(Node _ fs) = do rslt <- hoReduceProofTreeMemo (proofMemo checkerParams) (structuralRestriction t) t
                                                   case rslt of
                                                     Left msg -> (,) <$> (Node <$> pure (ProofError msg) <*> mapM (validateProofTree checkerParams >=> return . fst) fs) 
                                                                     <*> pure Nothing
                                                     Right seq ->  (,) <$> (Node <$> pure (ProofData (tbNotation (tableauCalc checkerParams) . show $ seq)) <*> mapM (validateProofTree checkerParams >=> return . fst) fs) 
                                                                    <*> pure (Just seq)
