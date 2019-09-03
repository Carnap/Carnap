{-# LANGUAGE FlexibleContexts, OverloadedStrings, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Action.SequentCheck (sequentCheckAction) where

import Lib
import Data.Tree
import Data.Map as M (lookup,Map)
import Data.Either
import Data.Aeson
import Data.Typeable (Typeable)
import Data.Aeson.Types
import Data.IORef (IORef, readIORef, newIORef)
import Control.Monad (join)
import qualified Text.Parsec as P (parse) 
import Control.Lens (view)
import Control.Concurrent
import GHCJS.DOM
import GHCJS.DOM.Types (Element, Document, IsElement, toJSString)
import GHCJS.DOM.Element (setInnerHTML)
import GHCJS.Types
#ifdef __GHCJS__
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
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

sequentCheckAction ::  IO ()
sequentCheckAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initCallbackObj
               initializeCallback "checkPropSequent" checkPropSequent
               initializeCallback "checkFOLSequent" checkFOLSequent
               initializeCallback "checkSequentInfo" checkFullSequentInfo
               initElements getCheckers activateChecker
               return ()

getCheckers :: IsElement self => Document -> self -> IO [Maybe (Element, Element, Map String String)]
getCheckers w = genInOutElts w "div" "div" "sequentchecker"

activateChecker :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateChecker _ Nothing  = return ()
activateChecker w (Just (i, o, opts))
        | sys == "propLK"  = setupWith gentzenPropLKCalc
        where sys = case M.lookup "system" opts of
                        Just s -> s
                        Nothing -> "propLK"

              setupWith calc = do
                  mseq <- parseGoal calc
                  root <- initRoot mseq o
                  threadRef <- newIORef (Nothing :: Maybe ThreadId)
                  checkOnChange threadRef root calc 

              parseGoal calc = do 
                  let seqParse = parseSeqOver $ tbParseForm calc
                  case M.lookup "goal" opts of
                      Just s -> case P.parse seqParse "" s of
                          Left e -> do setInnerHTML i (Just $ "Couldn't Parse This Goal:" ++ s)
                                       error "couldn't parse goal"
                          Right seq -> do setInnerHTML i (Just $ show seq) --will eventually want the equivalent of ndNotation
                                          return $ Just seq
                      Nothing -> return Nothing

checkOnChange :: IORef (Maybe ThreadId) -> JSVal -> TableauCalc lex sem r -> IO ()
checkOnChange threadRef root calc = return ()
--will need FFI to hook into root.on("changed") with an appropriate
--callback

initRoot :: Show a => Maybe a -> Element -> IO JSVal
initRoot Nothing elt = do root <- newRoot ""
                          renderOn elt root
                          return root
initRoot (Just s) elt = do root <- newRoot (show s)
                           renderOn elt root
                           return root

checkPropSequent :: Value -> IO Value
checkPropSequent v = do let Success t = parse parseReply v
                        case toTableau gentzenPropLKCalc t of 
                            Left feedback -> return . toInfo $ feedback
                            Right tab -> return . toInfo . validateTree $ tab

checkFOLSequent :: Value -> IO Value
checkFOLSequent v = do let Success t = parse parseReply v
                       case toTableau gentzenFOLKCalc t of 
                           Left feedback -> return . toInfo $ feedback
                           Right tab -> return . toInfo . validateTree $ tab

checkFullSequentInfo :: Value -> IO Value
checkFullSequentInfo v = do let Success t = parse fromInfo v
                            if t then return $ object [ "result" .= ("yes" :: String)]
                                 else return $ object [ "result" .= ("no" :: String)]

parseReply :: Value -> Parser (Tree (String,String))
parseReply = withObject "Sequent Tableau" $ \o -> do
    thelabel   <- o .: "label" :: Parser String
    therule <- o .: "rule" :: Parser String
    theforest <- o .: "forest" :: Parser [Value]
    filteredForest <- filter (\(Node (x,y) _) -> x /= "") <$> mapM parseReply theforest
    --ignore empty nodes
    return $ Node (thelabel,therule) filteredForest

toTableau :: ( Typeable sem
             , ReLex lex
             , Sequentable lex
             ) => TableauCalc lex sem rule -> Tree (String,String) -> Either TreeFeedback (Tableau lex sem rule)
toTableau calc (Node (l,r) f) 
    | all isRight parsedForest && isRight newNode = Node <$> newNode <*> sequence parsedForest
    | isRight newNode = Left $ Node Waiting (map cleanTree parsedForest)
    | Left n <- newNode = Left n
    where parsedLabel = P.parse (parseSeqOver (tbParseForm calc)) "" l
          parsedRule = if r == "" then pure Nothing else P.parse (Just <$> tbParseRule calc) "" r
          parsedForest = map (toTableau calc) f
          cleanTree (Left fs) = fs
          cleanTree (Right fs) = fmap (const Waiting) fs
          newNode = case TableauNode <$> parsedLabel <*> (pure Nothing) <*> parsedRule of
                        Right n -> Right n
                        Left e -> Left (Node (ParseErrorMsg (show e)) (map cleanTree parsedForest))

fromInfo :: Value -> Parser Bool
fromInfo = withObject "Info Tree" $ \o -> do
    theInfo <- o .: "info" :: Parser String
    theForest <- o .: "forest" :: Parser [Value]
    processedForest <- mapM fromInfo theForest
    return $ theInfo `elem` ["Correct", ""] && and processedForest

toInfo :: TreeFeedback -> Value
toInfo (Node Correct ss) = object [ "info" .= ("Correct" :: String), "class" .= ("correct" :: String), "forest" .= map toInfo ss]
toInfo (Node (Feedback e) ss) = object [ "info" .= e, "class" .= ("feedback" :: String), "forest" .= map toInfo ss]
toInfo (Node Waiting ss) = object [ "info" .= ("Waiting for parsing to be completed." :: String), "class" .= ("waiting" :: String), "forest" .= map toInfo ss]
toInfo (Node (ParseErrorMsg e) ss) = object [ "info" .= e, "class" .= ("parse-error" :: String), "forest" .= map toInfo ss]

#ifdef __GHCJS__

foreign import javascript unsafe "(function(){root = new ProofRoot({'label': $1,'forest': []}); return root})()" newRootJS :: JSString-> IO JSVal

foreign import javascript unsafe "$2.renderOn($1)" renderOnJS :: Element -> JSVal -> IO ()

newRoot :: String -> IO JSVal
newRoot s = newRootJS (toJSString s)

renderOn :: Element -> JSVal -> IO ()
renderOn elt root = renderOnJS elt root

#else

newRoot s = error "you need the JavaScript FFI to call newRoot"

renderOn :: Element -> JSVal -> IO ()
renderOn elt root = error "you need the JavaScript FFI to call renderOn"

#endif
