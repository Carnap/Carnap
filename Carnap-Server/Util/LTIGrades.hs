{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
module Util.LTIGrades (
    -- LTI Grade Sync Functions
    sendGradeToLMS
  , syncAllGradesForCourse
  , enableCourseGradeSync
  , disableCourseGradeSync
  , isGradeSyncEnabled
  , getLTIGradeData
  , GradeSyncStatus(..)
  , LTIUserGrade(..)
) where

import Import.NoFoundation
import qualified Control.Monad.Trans.Except as E
import qualified Yesod.Auth.LTI13 as LTI
import qualified Network.HTTP.Simple as HTTP
import qualified Data.Aeson as A
import qualified Data.Text as T
import Util.LTI
import Util.Grades
import Data.Aeson (encode, decodeStrict)
import Text.Printf (printf)

-- | LTI grade sync status for a course
data GradeSyncStatus
    = GradeSyncDisabled
    | GradeSyncEnabled
    | GradeSyncError Text
    deriving (Show, Generic)

instance ToJSON GradeSyncStatus
instance FromJSON GradeSyncStatus

-- | User grade data for LTI sync
data LTIUserGrade
    = LTIUserGrade
    { ltiUserId :: Text
    -- ^ Unique user identifier in the LMS
    , carnapUserId :: Key User
    -- ^ User ID in Carnap
    , gradeValue :: Double
    -- ^ Calculated grade (0.0 to 1.0)
    , assignmentLabel :: Text
    -- ^ Assignment/assessment label
    , lastUpdated :: UTCTime
    -- ^ Last update timestamp
    } deriving (Show, Generic)

instance ToJSON LTIUserGrade
instance FromJSON LTIUserGrade

-- | LTI grade API payload structure
data LTIGradePayload
    = LTIGradePayload
    { scoreGiven :: Double
    -- ^ Grade to send (0.0 to 1.0)
    , scoreMaximum :: Double
    -- ^ Maximum grade (typically 1.0)
    , comment :: Maybe Text
    -- ^ Optional comment
    , timestamp :: Text
    -- ^ ISO 8601 timestamp
    } deriving (Show, Generic)

instance ToJSON LTIGradePayload where
    toJSON (LTIGradePayload scoreGiven scoreMaximum comment timestamp) =
        object [ "scoreGiven" .= scoreGiven
               , "scoreMaximum" .= scoreMaximum
               , "comment" .= comment
               , "timestamp" .= timestamp
               ]

-- | Enable grade synchronization for a course
enableCourseGradeSync :: Key Course -> HandlerFor App ()
enableCourseGradeSync courseId = do
    runDB $ upsertBy (UniqueGradeSyncStatus courseId)
        GradeSyncStatus
            { gradeSyncStatusCourse = courseId
            , gradeSyncStatusEnabled = True
            , gradeSyncStatusLastError = Nothing
            }
        [ GradeSyncStatusEnabled =. True
        , GradeSyncStatusLastError =. Nothing
        ]

-- | Disable grade synchronization for a course
disableCourseGradeSync :: Key Course -> HandlerFor App ()
disableCourseGradeSync courseId = do
    runDB $ upsertBy (UniqueGradeSyncStatus courseId)
        GradeSyncStatus
            { gradeSyncStatusCourse = courseId
            , gradeSyncStatusEnabled = False
            , gradeSyncStatusLastError = Nothing
            }
        [ GradeSyncStatusEnabled =. False
        , GradeSyncStatusLastError =. Nothing
        ]

-- | Check if grade synchronization is enabled for a course
isGradeSyncEnabled :: Key Course -> HandlerFor App GradeSyncStatus
isGradeSyncEnabled courseId = do
    mStatus <- runDB $ getBy $ UniqueGradeSyncStatus courseId
    case mStatus of
        Nothing -> return GradeSyncDisabled
        Just (Entity _ rec) -> 
            if gradeSyncStatusEnabled rec 
            then return GradeSyncEnabled
            else case gradeSyncStatusLastError rec of
                Just err -> return $ GradeSyncError err
                Nothing -> return GradeSyncDisabled

-- | Get grade data for all LTI users in a course
getLTIGradeData :: Key Course -> Key Assignment -> HandlerFor App [LTIUserGrade]
getLTIGradeData courseId assignmentId = do
    ltiUsers <- runDB $ selectList
        [ UserDataEnrolledIn ==. Just courseId
        , UserDataIsLti ==. True
        ] []
    
    assignment <- runDB $ get404 assignmentId
    
    mapM (\(Entity uid userData) -> do
        submissions <- runDB $ selectList
            [ ProblemSubmissionUserId ==. uid
            , ProblemSubmissionAssignmentId ==. Just assignmentId
            , ProblemSubmissionCorrect ==. True
            ] []
        
        totalScore <- calculateTotalScore uid submissions
        let grade = min 1.0 (fromIntegral totalScore / 100.0)
        
        return LTIUserGrade
            { ltiUserId = fromMaybe (pack . show $ uid) (userDataUniversityId userData)
            , carnapUserId = uid
            , gradeValue = grade
            , assignmentLabel = assignmentMetadataTitle assignment
            , lastUpdated = now
            })
        ltiUsers
  where
    now = liftIO getCurrentTime

-- | Synchronize all grades for a course with the LMS
syncAllGradesForCourse :: Key Course -> Key Assignment -> HandlerFor App (Int, Int)
syncAllGradesForCourse courseId assignmentId = do
    syncStatus <- isGradeSyncEnabled courseId
    case syncStatus of
        GradeSyncDisabled -> return (0, 0)
        GradeSyncError err -> do
            $logError $ "Grade sync error for course " <> tshow courseId <> ": " <> err
            return (0, 0)
        GradeSyncEnabled -> do
            gradeData <- getLTIGradeData courseId assignmentId
            results <- mapM (sendGradeToLMS courseId) gradeData
            let successful = length $ filter id results
                failed = length results - successful
            
            $logInfo $ printf "Grade sync completed for course %s: %d successful, %d failed" 
                (show courseId) successful failed
            
            return (successful, failed)

-- | Send individual grade to LMS via LTI
sendGradeToLMS :: Key Course -> LTIUserGrade -> HandlerFor App Bool
sendGradeToLMS courseId LTIUserGrade{ltiUserId, gradeValue, assignmentLabel} = do
    app <- getYesod
    case appLtiPlatforms app of
        Nothing -> do
            $logError "No LTI platforms configured"
            recordGradeSyncError courseId "No LTI platforms configured"
            return False
        Just platforms -> do
            mPlatform <- findLTIPlatformForCourse platforms courseId
            case mPlatform of
                Nothing -> do
                    $logError $ "No LTI platform found for course " <> tshow courseId
                    recordGradeSyncError courseId "No LTI platform found for course"
                    return False
                Just platform -> do
                    success <- sendGradeToLTIPlatform platform ltiUserId gradeValue assignmentLabel
                    if success 
                    then $logInfo $ printf "Successfully sent grade %.2f for user %s" 
                        gradeValue (unpack ltiUserId)
                    else $logError $ printf "Failed to send grade for user %s" (unpack ltiUserId)
                    return success

-- | Send grade to specific LTI platform
sendGradeToLTIPlatform :: PlatformInfo -> Text -> Double -> Text -> HandlerFor App Bool
sendGradeToLTIPlatform platform userId gradeValue assignmentLabel = do
    let gradePayload = LTIGradePayload
            { scoreGiven = gradeValue
            , scoreMaximum = 1.0
            , comment = Just $ "Grade from Carnap assignment: " <> assignmentLabel
            , timestamp = T.pack $ formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%SZ" (unsafePerformIO getCurrentTime)
            }
    
    let baseUrl = platformOidcAuthEndpoint platform
        gradeUrl = baseUrl <> "/api/rest/v1/lineitems/score"
    
    mToken <- getLTIAccessToken platform userId
    case mToken of
        Nothing -> do
            $logError $ "Failed to get LTI access token for user " <> userId
            return False
        Just token -> do
            request <- HTTP.parseRequest (unpack gradeUrl)
            let request' = HTTP.setRequestMethod "POST"
                        . HTTP.setRequestHeader "Authorization" ["Bearer " <> encodeUtf8 token]
                        . HTTP.setRequestHeader "Content-Type" ["application/json"]
                        . HTTP.setRequestBodyJSON gradePayload
                        $ request
            
            result <- liftIO $ HTTP.httpBS request'
            case HTTP.getResponseStatusCode result of
                200 -> return True
                _ -> do
                    let status = HTTP.getResponseStatus result
                    $logError $ printf "LTI grade sync failed: %d %s" 
                        (statusCode status) (statusMessage status)
                    return False

-- | Find LTI platform associated with a course
findLTIPlatformForCourse :: [PlatformInfo] -> Key Course -> HandlerFor App (Maybe PlatformInfo)
findLTIPlatformForCourse platforms courseId = do
    mAutoreg <- runDB $ getBy $ UniqueCourseAutoreg courseId
    case mAutoreg of
        Nothing -> return Nothing
        Just (Entity _ autoreg) -> do
            let issuer = courseAutoregIssuer autoreg
                deploymentId = courseAutoregDeploymentId autoreg
            return $ find (\p -> platformIssuer p == issuer && platformClientId p == deploymentId) platforms

-- | Get LTI access token for a user
getLTIAccessToken :: PlatformInfo -> Text -> HandlerFor App (Maybe Text)
getLTIAccessToken platform userId = do
    return Nothing

-- | Record grade sync error
recordGradeSyncError :: Key Course -> Text -> HandlerFor App ()
recordGradeSyncError courseId errorMsg = do
    runDB $ upsertBy (UniqueGradeSyncStatus courseId)
        GradeSyncStatus
            { gradeSyncStatusCourse = courseId
            , gradeSyncStatusEnabled = True
            , gradeSyncStatusLastError = Just errorMsg
            }
        [ GradeSyncStatusLastError =. Just errorMsg
        ]

-- | Calculate total score from submissions
calculateTotalScore :: Key User -> [Entity ProblemSubmission] -> HandlerFor App Int
calculateTotalScore uid submissions = do
    -- Get course from first submission to determine accommodation
    case submissions of
        [] -> return 0
        (Entity _ firstSubmission:_) -> do
            mCourse <- getCourseForSubmission firstSubmission
            case mCourse of
                Nothing -> return 0
                Just courseId -> do
                    accommodation <- getUserAccommodation courseId uid
                    textbookproblems <- getGlobalProblemSets
                    
                    foldM (\total (Entity _ submission) -> do
                        score <- toScore uid accommodation textbookproblems submission
                        return $ total + score
                    ) 0 submissions

-- | Get course for a submission
getCourseForSubmission :: ProblemSubmission -> HandlerFor App (Maybe (Key Course))
getCourseForSubmission submission = do
    case problemSubmissionAssignmentId submission of
        Just assignmentId -> do
            mAssignment <- runDB $ get assignmentId
            return $ fmap assignmentMetadataCourse mAssignment
        Nothing -> return Nothing

-- | Get user accommodation for a course
getUserAccommodation :: Key Course -> Key User -> HandlerFor App Int
getUserAccommodation courseId uid = do
    mAcc <- runDB $ getBy $ UniqueAccommodation courseId uid
    return $ maybe 0 (accommodationDateExtraHours . entityVal) mAcc

-- | Get global problem sets (placeholder)
getGlobalProblemSets :: HandlerFor App (Maybe BookAssignmentTable)
getGlobalProblemSets = return Nothing