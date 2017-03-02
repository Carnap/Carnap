{-# LANGUAGE RankNTypes, OverloadedStrings, FlexibleContexts, DeriveDataTypeable, CPP, JavaScriptFFI #-}

module Carnap.GHCJS.Action.AcceptJSON
        ( acceptJSONAction) where

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
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PurePropositional.Parser
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)

acceptJSONAction ::  IO ()
acceptJSONAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initializeCallback checkJSON
               return ()

checkJSON:: Value -> IO String
checkJSON v = do let Success (s,d,c,p) = parse parseReply v
                 print $ show d
                 case parseProofData d of
                     Left e -> return $ "parsing error: " ++ show e
                     Right ded -> do let Feedback mseq ds = toDisplaySequenceStructured processLineStructuredFitch ded
                                     print "errors:"
                                     print $ map wrap ds
                                     return $ show mseq 
                                      

parseReply = withObject "not an object" $ \o -> do
    psetting <- o .: "predicateSettings" :: Parser Bool
    proofdata <- o .: "proofData" :: Parser Value
    wantedconc <- o .: "wantedConclusion" :: Parser String
    numPrems <- o .: "numPrems" :: Parser Int
    return (psetting, proofdata, wantedconc, numPrems)

parseProofData :: Value -> Either P.ParseError (DeductionTree LogicBookPropLogic PurePropLexicon)
parseProofData valList = evalStateT (process valList) 1
    where
    process :: Value -> StateT Int (Either P.ParseError) (DeductionTree LogicBookPropLogic PurePropLexicon)
    process v = case parse parseJSON v :: Result [Value] of
                    Success vl -> do n <- get
                                     list <- toList vl
                                     m <- get
                                     return $ SubProof (n,m - 1) list
                    Error e -> error "bad json"

    toList :: [Value] -> StateT Int (Either P.ParseError) [DeductionTree LogicBookPropLogic PurePropLexicon]
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

    splitLine :: Object -> Parser (String,String)
    splitLine o = do wff <- o .: "wffstr"
                     jst <- o .: "jstr"
                     let jst' = case jst of
                            "Pr" -> "PR"
                            "Hyp" -> "AS"
                            x -> x
                     return (wff,jst')

    parsePair (wff,jstr) = AssertLine <$> P.parse (purePropFormulaParser "ABCDEFGHIJKLMNOPQRSTUVWXYZ") "" wff
                                      <*> (fst <$> P.parse (parseJstr $ parseFitchPropLogic M.empty) "" jstr)
                                      <*> return 0
                                      <*> (snd <$> P.parse (parseJstr $ parseFitchPropLogic M.empty) "" jstr)

    parseJstr r = do rule <- spaces *> r
                     deps <- spaces *> many (try parseIntPair <|> parseInt)
                     return (rule,deps)

    parseIntPair = do P.spaces
                      i1 <- many1 digit
                      char '–'  
                      i2 <- many1 digit
                      spaces
                      return ((read i1, read i2) :: (Int,Int))

    parseInt= do spaces
                 i <- many1 digit
                 spaces
                 return ((read i, read i) :: (Int,Int))

wrap (Left (GenericError s n))  = "?" ++ s ++ " on line " ++ show n 
wrap (Left (NoParse e n))       = "⚠ Can't read this line. There may be a typo."++ show e
wrap (Left (NoUnify eqs n))     = "Can't match these premises with this conclusion, using this rule"
wrap (Left (NoResult _))        = "<div>&nbsp;</div>"
wrap (Right s)                  = "<div>+<div><div>" ++ show s ++ "<div></div></div>"

#ifdef __GHCJS__

foreign import javascript unsafe "acceptJSONCallback_ = $1" initializeCallbackJS :: Callback (payload -> succ -> IO ()) -> IO ()

foreign import javascript unsafe "$1($2);" simpleCall :: JSVal -> JSString -> IO ()

initializeCallback :: (Value -> IO String) -> IO ()
initializeCallback f = do theCB <- asyncCallback2 (cb f)
                          initializeCallbackJS theCB
    where cb f payload succ = do (Just raw) <- fromJSVal payload
                                 let (Just val) = decode . fromStrict . encodeUtf8 $ raw
                                 rslt <- f val
                                 return ()
                                 simpleCall succ (toJSString rslt)

#else

initializeCallback :: (Value -> IO String) -> IO ()
initializeCallback = undefined

#endif
