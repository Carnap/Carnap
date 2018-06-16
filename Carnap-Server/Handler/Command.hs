module Handler.Command where

import Import
import Carnap.GHCJS.SharedTypes
-- XXX: It would be nice for this to be more generic
import Carnap.Languages.PurePropositional.Logic (DerivedRule)
import Data.Aeson (encode, decodeStrict)
import Data.Time
import Util.Database
import Util.Data
import Text.Read (read)

postCommandR :: Handler Value
postCommandR = do
    cmd  <- requireJsonBody :: Handler GHCJSCommand

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just uid  -> case cmd of
                EchoBack (s,b) -> returnJson (reverse s)
                Submit typ ident dat source correct partial key ->  
                    do let key' = case key of "" -> Nothing; s -> Just (read s)
                       time <- liftIO getCurrentTime
                       let sub = ProblemSubmission (pack ident) dat typ time uid correct partial source key'
                       success <- tryInsert sub
                       afterInsert success
                SaveDerivedRule n dr -> do time <- liftIO getCurrentTime
                                           let save = SavedDerivedRule (toStrict $ encode dr) (pack n) time uid
                                           tryInsert save >>= afterInsert
                RequestDerivedRulesForUser -> do savedRules <- runDB $ selectList [SavedDerivedRuleUserId ==. uid] []
                                                 let packagedRules = catMaybes $ map (packageRule . entityVal) savedRules
                                                 liftIO $ print $ "sending" ++ (show $ toJSON packagedRules)
                                                 returnJson $ show $ toJSON packagedRules

packageRule (SavedDerivedRule dr n _ _) = case (decodeStrict dr :: Maybe DerivedRule) of
                                              Just r -> Just (unpack n, r)
                                              _ -> Nothing

afterInsert success = if success then returnJson ("submitted!" :: String) 
                                 else returnJson ("Clash" :: String)
