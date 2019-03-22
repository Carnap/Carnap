module Handler.Command where

import Import
import Carnap.GHCJS.SharedTypes
-- XXX: It would be nice for this to be more generic
import Data.Aeson (encode, decodeStrict)
import Data.Time
import Util.Database
import Util.Data
import Text.Read (readMaybe)

postCommandR :: Handler Value
postCommandR = do
    cmd  <- requireJsonBody :: Handler GHCJSCommand

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just uid  -> case cmd of
                Submit typ ident dat source correct credit key ->  
                    do time <- liftIO getCurrentTime
                       (mkey, masgn) <- case key of 
                                        "" -> return (Nothing,Nothing)
                                        s -> case readMaybe s of
                                                 Just akey -> 
                                                    do masgn <- runDB (get akey)
                                                       case masgn of 
                                                            Nothing -> invalidArgs ["Cannot look up assignment key"]
                                                            Just asgn -> return (Just akey, Just asgn)
                                                 Nothing -> invalidArgs ["Unparsable assignment key"]
                       let sub = ProblemSubmission 
                                    { problemSubmissionIdent = (pack ident)
                                    , problemSubmissionData = dat
                                    , problemSubmissionType = typ
                                    , problemSubmissionTime = time
                                    , problemSubmissionUserId = uid
                                    , problemSubmissionCorrect = correct
                                    , problemSubmissionCredit = credit
                                    , problemSubmissionExtra = Nothing
                                    , problemSubmissionSource = source
                                    , problemSubmissionAssignmentId = mkey
                                    }
                       case (mkey,masgn) of 
                            (Nothing,Nothing) -> 
                                do success <- tryInsert sub
                                   afterInsert success
                            (Just ak, Just asgn) ->
                                if assignmentMetadataVisibleTill asgn > Just time
                                   || assignmentMetadataVisibleTill asgn == Nothing
                                   then do success <- tryInsert sub
                                           afterInsert success
                                   else returnJson ("Assignment not available" :: String)
                SaveRule n r -> do time <- liftIO getCurrentTime
                                   let save = SavedRule r (pack n) time uid
                                   tryInsert save >>= afterInsert
                RequestDerivedRulesForUser -> do savedPropRules <- runDB $ selectList [SavedDerivedRuleUserId ==. uid] []
                                                 savedRules <- runDB $ selectList [SavedRuleUserId ==. uid] []
                                                 let oldRules = catMaybes $ map (packageOldRule . entityVal) savedPropRules
                                                     newRules = map (packageNewRule . entityVal) savedRules
                                                     rules = oldRules ++ newRules
                                                 liftIO $ print $ "sending" ++ (show $ toJSON rules)
                                                 returnJson $ show $ toJSON $ rules

packageOldRule (SavedDerivedRule dr n _ _) = case decodeRule dr of
                                                Just r -> Just (unpack n, PropRule r)
                                                _ -> Nothing

packageNewRule (SavedRule dr n _ _) = (unpack n, dr)

afterInsert (Just _) = returnJson ("submitted!" :: String) 
afterInsert Nothing = returnJson ("Clash" :: String)
