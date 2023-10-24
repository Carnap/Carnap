{-# LANGUAGE UndecidableInstances, FlexibleInstances, RankNTypes, OverloadedStrings, FlexibleContexts, DeriveDataTypeable, CPP, JavaScriptFFI #-}

module Carnap.GHCJS.Action.AcceptJSON
        ( acceptJSONAction ) where

import Data.Tree as T
import qualified Data.Map as M
import Data.Aeson as A
import Data.Foldable
import Data.Aeson.Types
import Data.Text.Encoding
import Data.ByteString.Lazy (fromStrict)
import Control.Monad.State
import qualified Text.Parsec as P
import Text.Parsec (many, digit, spaces, try, many1, char, (<|>))
#ifdef __GHCJS__
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
import GHCJS.DOM
import GHCJS.DOM.Types
import Carnap.Core.Data.Types (Form, FixLang,)
import Carnap.Core.Data.Classes (Schematizable,UniformlyEq(..))
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PureFirstOrder.Logic
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.ClassicalSequent.Syntax

acceptJSONAction ::  IO ()
acceptJSONAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initializeCallback initializeCallbackJS checkJSON
               initializeCallback initializeCallbackJSGallow checkJSONGallow
               return ()

checkJSON:: Value -> IO Value
checkJSON v = do let Success (s,d,c,p) = parse parseReply v
                 print (s,d,c,p)
                 --- XXX See if this duplication can be avoided
                 if s then case (parseProofData parsePairFOL d, P.parse magnusFOLFormulaParser "" c) of
                        (Left e,_) -> return $ replyObject False "" nilson (show e)
                        (Right ded,Right conc) -> 
                            do let Feedback mseq ds = toDisplaySequenceStructured processLineStructuredFitchHO ded
                               let fb = toJSON $ map serialize ds
                               return $ case mseq of 
                                  Just seq@(_:|-: (SS s)) -> replyObject (s =* liftToSequent conc) (show seq) fb ""
                                  Nothing ->  replyObject False "" fb ""
                        (_,Left e) -> return $ replyObject False "" nilson "couldn't parse conclusion"
                      else case (parseProofData parsePairProp d, P.parse (purePropFormulaParser extendedLetters) "" c) of
                        (Left e,_) -> return $ replyObject False "" nilson (show e)
                        (Right ded, Right conc) -> 
                            do let Feedback mseq ds = toDisplaySequenceStructured processLineStructuredFitch ded
                               let fb = toJSON $ map serialize ds
                               return $ case mseq of 
                                  Just seq@(_:|-: (SS s)) -> replyObject (s =* liftToSequent conc) (show seq) fb ""
                                  Nothing ->  replyObject False "" fb ""
                        (_,Left e) -> return $ replyObject False "" nilson "couldn't parse conclusion"

    where serialize (Left e) = Left e
          serialize (Right s) = Right $ show s
          nilson = toJSON ("" :: String)

checkJSONGallow:: Value -> IO Value
checkJSONGallow v = do let Success (s,d,c,p) = parse parseReply v
                       print (s,d,c,p)
                       --- XXX See if this duplication can be avoided
                       if s then case (parseProofData parsePairFOLGallow d, P.parse gallowPLFormulaParser "" c) of
                                (Left e,_) -> return $ replyObject False "" nilson (show e)
                                (Right ded,Right conc) -> 
                                    do let Feedback mseq ds = toDisplaySequenceStructured processLineStructuredFitchHO ded
                                       let fb = toJSON $ map serialize ds
                                       return $ case mseq of 
                                            Just seq@(_:|-: (SS s)) -> replyObject (s =* liftToSequent conc) (show seq) fb ""
                                            Nothing ->  replyObject False "" fb ""
                                (_,Left e) -> return $ replyObject False "" nilson "couldn't parse conclusion"
                            else case (parseProofData parsePairPropGallow d, P.parse (purePropFormulaParser thomasBolducZach2019Opts) "" c) of
                                (Left e,_) -> return $ replyObject False "" nilson (show e)
                                (Right ded, Right conc) -> 
                                    do let Feedback mseq ds = toDisplaySequenceStructured processLineStructuredFitch ded
                                       let fb = toJSON $ map serialize ds
                                       return $ case mseq of 
                                            Just seq@(_:|-: (SS s)) -> replyObject (s =* liftToSequent conc) (show seq) fb ""
                                            Nothing ->  replyObject False "" fb ""
                                (_,Left e) -> return $ replyObject False "" nilson "couldn't parse conclusion"

    where serialize (Left e) = Left e
          serialize (Right s) = Right $ show s
          nilson = toJSON ("" :: String)

replyObject succeeded sequent feedback errmsg = object [ "succeed" .= (succeeded :: Bool)
                                                       , "sequent" .= (sequent :: String)
                                                       , "feedback" .= (feedback :: Value)
                                                       , "errmsg" .= (errmsg :: String)
                                                       ]
                                      
parseReply = withObject "not an object" $ \o -> do
    psetting   <- o .: "predicateSettings" :: Parser Bool
    proofdata  <- o .: "proofData" :: Parser Value
    wantedconc <- o .: "wantedConclusion" :: Parser String
    numPrems   <- o .: "numPrems" :: Parser Int
    return (psetting, proofdata, wantedconc, numPrems)

parseProofData :: ((String,String) -> Either P.ParseError (DeductionLine r lex (Form Bool))) -> Value -> Either P.ParseError (DeductionTree r lex (Form Bool))
parseProofData parsePair valList = evalStateT (process valList) 1
    where
    process v = case parse parseJSON v :: Result [Value] of
                    Success vl -> do n <- get
                                     list <- toList vl
                                     m <- get
                                     return $ SubProof (n,m - 1) list
                    Error e -> error "bad json"

    toList vl = case vl of
                   [] -> return []
                   (o:vl') -> case parse (withObject "" splitLine) o of
                                 Success pair -> do n <- get
                                                    o' <- lift $ Leaf n <$> parsePair pair
                                                    modify (+ 1) 
                                                    vl'' <- toList vl'
                                                    return $ o' : vl''
                                 Error e -> do o' <- process o 
                                               vl'' <- toList vl'
                                               return $ o' : vl''

    splitLine o = do wff <- o .: "wffstr"
                     jst <- o .: "jstr"
                     let jst' = case jst of
                            "Pr" -> "PR"
                            "Hyp" -> "AS"
                            x -> x
                     return (wff,jst')

parsePairProp (wff,jstr) = AssertLine <$> P.parse (purePropFormulaParser extendedLetters) "" wff
                                      <*> (fst <$> P.parse (parseJstr $ parseMagnusSL (defaultRuntimeDeductionConfig)) "" jstr)
                                      <*> return 0
                                      <*> (snd <$> P.parse (parseJstr $ parseMagnusSL (defaultRuntimeDeductionConfig)) "" jstr)

parsePairFOL  (wff,jstr) = AssertLine <$> P.parse magnusFOLFormulaParser "" wff
                                      <*> (fst <$> P.parse (parseJstr $ parseMagnusQL (defaultRuntimeDeductionConfig)) "" jstr)
                                      <*> return 0
                                      <*> (snd <$> P.parse (parseJstr $ parseMagnusQL (defaultRuntimeDeductionConfig)) "" jstr)

parsePairPropGallow (wff,jstr) = AssertLine <$> P.parse (purePropFormulaParser thomasBolducZach2019Opts) "" wff
                                      <*> (fst <$> P.parse (parseJstr $ parseGallowSL (defaultRuntimeDeductionConfig)) "" jstr)
                                      <*> return 0
                                      <*> (snd <$> P.parse (parseJstr $ parseGallowSL (defaultRuntimeDeductionConfig)) "" jstr)

parsePairFOLGallow  (wff,jstr) = AssertLine <$> P.parse gallowPLFormulaParser "" wff
                                      <*> (fst <$> P.parse (parseJstr $ parseGallowPL (defaultRuntimeDeductionConfig)) "" jstr)
                                      <*> return 0
                                      <*> (snd <$> P.parse (parseJstr $ parseGallowPL (defaultRuntimeDeductionConfig)) "" jstr)

parseJstr r = do rule <- spaces *> r
                 deps <- spaces *> many (try parseIntPair <|> parseInt)
                 return (rule,deps)

parseIntPair = do P.spaces
                  i1 <- many1 digit
                  char '–'  
                  i2 <- many1 digit
                  spaces
                  return ((read i1, read i2) :: (Int,Int))

parseInt = do spaces
              i <- many1 digit
              spaces
              return ((read i, read i) :: (Int,Int))

instance (Schematizable (FixLang lex), Schematizable (ClassicalSequentOver lex)) => ToJSON (ProofErrorMessage lex) where
        toJSON (GenericError s n) = object [ "errorType" .= ("GenericError" :: String)
                                           , "message" .= s
                                           , "lineNo" .= n
                                           ]
        toJSON (NoParse e n) = object      [ "errorType" .= ("NoParse" :: String)
                                           , "message" .= show e
                                           , "lineNo" .= n
                                           ]
        toJSON (NoUnify eqs n) = object    [ "errorType" .= ("NoUnify" :: String)
                                           , "message" .= ("could not apply this rule" :: String)
                                           , "equations" .= map (map show) eqs
                                           , "lineNo" .= n
                                           ]
        toJSON (NoResult n)    = object    [ "errorType" .= ("NoResult" :: String)
                                           , "message" .= ("" :: String)
                                           , "lineNo" .= n
                                           ]

#ifdef __GHCJS__

foreign import javascript unsafe "acceptJSONCallback_ = $1" initializeCallbackJS :: Callback (payload -> succ -> IO ()) -> IO ()
foreign import javascript unsafe "acceptJSONCallbackGallow_ = $1" initializeCallbackJSGallow :: Callback (payload -> succ -> IO ()) -> IO ()
--TODO: unify with other callback code in SequentCheck

foreign import javascript unsafe "$1($2);" simpleCall :: JSVal -> JSVal -> IO ()
foreign import javascript unsafe "console.error('could not parse input');" jsError :: IO ()

initializeCallback :: (Callback (JSVal -> JSVal -> IO ()) -> IO ()) -> ((Value -> IO Value) -> IO ())
initializeCallback jscb f = do theCB <- asyncCallback2 (cb f)
                               jscb theCB
    where cb f payload succ = do (Just raw) <- fromJSVal payload
                                 let dc = decode . fromStrict . encodeUtf8 $ raw
                                 case dc of
                                    Just val -> do rslt <- f val
                                                   rslt' <- toJSVal rslt
                                                   simpleCall succ rslt'
                                    Nothing -> jsError

#else

initializeCallback :: (Value -> IO Value) -> IO ()
initializeCallback = undefined

#endif
