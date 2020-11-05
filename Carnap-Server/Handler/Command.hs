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
           Nothing -> returnJson ("You need to be logged in to submit work." :: String)
           Just uid  -> case cmd of
                Submit typ ident dat source correct credit late key ->  
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
                                    , problemSubmissionLateCredit = late
                                    , problemSubmissionExtra = Nothing
                                    , problemSubmissionSource = source
                                    , problemSubmissionAssignmentId = mkey
                                    }
                       case (mkey,masgn) of 
                            (Nothing,Nothing) -> 
                                do success <- tryInsert sub
                                   afterInsert success
                            (Just ak, Just asgn) -> do
                                (mtoken,maccess,mex) <- runDB $ (,,) 
                                    <$> (getBy $ UniqueAssignmentAccessToken uid ak)
                                    <*> (getBy $ UniqueAccommodation (assignmentMetadataCourse asgn) uid)
                                    <*> (getBy $ UniqueExtension ak uid)
                                let age (Entity _ tok) = floor (diffUTCTime time (assignmentAccessTokenCreatedAt tok))
                                    accommodationFactor = maybe 1 (accommodationTimeFactor . entityVal) maccess
                                    accommodationMinutes = maybe 0 (accommodationTimeExtraMinutes . entityVal) maccess
                                    testTime min = floor ((fromIntegral min) * accommodationFactor) + accommodationMinutes
                                case (mtoken, assignmentMetadataAvailability asgn) of
                                     (Just tok, Just (ViaPasswordExpiring _ min)) | age tok > 60 * testTime min 
                                            -> returnJson ("Assignment time limit exceeded" :: String)
                                     (Just tok, Just (HiddenViaPasswordExpiring _ min)) | age tok > 60 * testTime min 
                                            -> returnJson ("Assignment time limit exceeded" :: String)
                                     _ | assignmentMetadataVisibleTill asgn > Just time -> tryInsert sub >>= afterInsert
                                       | null (assignmentMetadataVisibleTill asgn) -> tryInsert sub >>= afterInsert
                                       | (extensionUntil . entityVal <$> mex) > Just time -> tryInsert sub >>= afterInsert
                                       | otherwise -> returnJson ("Assignment not available" :: String)
                SaveRule n r | null n -> returnJson ("The rule needs a nonempty name." :: String)
                SaveRule n r -> do time <- liftIO getCurrentTime
                                   let save = SavedRule r (pack n) time uid
                                   tryInsert save >>= afterInsert
                RequestDerivedRulesForUser -> do savedPropRules <- runDB $ selectList [SavedDerivedRuleUserId ==. uid] []
                                                 savedRules <- runDB $ selectList [SavedRuleUserId ==. uid] []
                                                 let oldRules = catMaybes $ map (packageOldRule . entityVal) savedPropRules
                                                     newRules = map (packageNewRule . entityVal) savedRules
                                                     rules = oldRules ++ newRules
                                                 returnJson $ show $ toJSON $ rules

packageOldRule (SavedDerivedRule dr n _ _) = case decodeRule dr of
                                                Just r -> Just (unpack n, PropRule r)
                                                _ -> Nothing

packageNewRule (SavedRule dr n _ _) = (unpack n, dr)

afterInsert (Just _) = returnJson ("submitted!" :: String) 
afterInsert Nothing = returnJson ("It appears you've already successfully submitted this problem." :: String)
