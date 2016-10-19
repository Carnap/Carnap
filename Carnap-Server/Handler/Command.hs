module Handler.Command where

import Import
import Carnap.GHCJS.SharedTypes
-- XXX: It would be nice for this to be more generic
import Carnap.Languages.PurePropositional.Logic (DerivedRule)
import Data.Aeson (encode, decodeStrict)
import Model (SyntaxCheckSubmission,TranslationSubmission)
import Data.Time 

postCommandR :: Handler Value
postCommandR = do
    cmd  <- requireJsonBody :: Handler GHCJSCommand

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just u  -> case cmd of
                EchoBack (s,b) -> returnJson (reverse s)
                SubmitSyntaxCheck f -> submit SyntaxCheckSubmission f u  >>= afterInsert
                SubmitTranslation f -> submit TranslationSubmission f u  >>= afterInsert
                SubmitTruthTable f  -> submit TruthTableSubmission f u   >>= afterInsert
                SubmitDerivation s d -> do time <- liftIO getCurrentTime               
                                           let sub = DerivationSubmission (pack s) (pack d) (pack $ show time) u 
                                           tryInsert sub >>= afterInsert
                SaveDerivedRule n dr -> do time <- liftIO getCurrentTime
                                           let save = SavedDerivedRule (toStrict $ encode dr) (pack n) (pack $ show time) u
                                           tryInsert save >>= afterInsert
                RequestDerivedRulesForUser -> do savedRules <- runDB $ selectList [SavedDerivedRuleUserId ==. u] []
                                                 let packagedRules = map (packageRule . entityVal) savedRules
                                                 returnJson $ catMaybes packagedRules

packageRule (SavedDerivedRule dr n _ _) = case (decodeStrict dr :: Maybe DerivedRule) of
                                              Just r -> Just (unpack n, r)
                                              _ -> Nothing

submit typ f u = do time <- liftIO getCurrentTime
                    let sub = typ (pack f) (pack $ show time) u
                    tryInsert sub

tryInsert s = runDB $ do munique <- checkUnique s
                         case munique of                  
                              (Just _) -> return False    
                              Nothing  -> do insert s
                                             return True

afterInsert success = if success then returnJson ("submitted!" :: String) 
                                 else returnJson ("Clash" :: String)
