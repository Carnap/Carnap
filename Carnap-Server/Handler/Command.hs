module Handler.Command where

import Import
import Carnap.GHCJS.SharedTypes
-- XXX: It would be nice for this to be more generic
import Carnap.Languages.PurePropositional.Logic (DerivedRule)
import Data.Aeson (encode, decodeStrict)
import Model (SyntaxCheckSubmission,TranslationSubmission)
import Data.Time
import Util.Database
import Util.Data

postCommandR :: Handler Value
postCommandR = do
    cmd  <- requireJsonBody :: Handler GHCJSCommand

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just u  -> case cmd of
                EchoBack (s,b) -> returnJson (reverse s)
                SubmitSyntaxCheck f  Book -> submit SyntaxCheckSubmission f u CarnapTextbook
                SubmitTranslation f  Book -> submit TranslationSubmission f u CarnapTextbook
                SubmitTruthTable f   Book -> submit TruthTableSubmission f u CarnapTextbook
                SubmitDerivation s d Book -> do time <- liftIO getCurrentTime               
                                                let sub = DerivationSubmission (pack s) (pack d) 
                                                                  (pack $ show time) u CarnapTextbook
                                                tryInsert sub >>= afterInsert
                SaveDerivedRule n dr -> do time <- liftIO getCurrentTime
                                           let save = SavedDerivedRule (toStrict $ encode dr) (pack n) (pack $ show time) u
                                           tryInsert save >>= afterInsert
                RequestDerivedRulesForUser -> do savedRules <- runDB $ selectList [SavedDerivedRuleUserId ==. u] []
                                                 let packagedRules = catMaybes $ map (packageRule . entityVal) savedRules
                                                 liftIO $ print $ "sending" ++ (show $ toJSON packagedRules)
                                                 returnJson $ show $ toJSON packagedRules

packageRule (SavedDerivedRule dr n _ _) = case (decodeStrict dr :: Maybe DerivedRule) of
                                              Just r -> Just (unpack n, r)
                                              _ -> Nothing

submit typ f u c = do time <- liftIO getCurrentTime
                      let sub = typ (pack f) (pack $ show time) u c
                      success <- tryInsert sub
                      afterInsert success

afterInsert success = if success then returnJson ("submitted!" :: String) 
                                 else returnJson ("Clash" :: String)
