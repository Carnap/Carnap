module Handler.API.Instructor.Assignments where

import           Data.Aeson
import           Data.Time
import           Data.Time.Zones
import           Data.Time.Zones.DB
import           Data.Time.Zones.All
import           Data.HashMap.Strict as HM
import           Import
import           Util.Data           (SharingScope (..), AvailabilityStatus (..))
import           Util.Handler
import           Util.Database (problemQuery)
import           System.Directory
import           System.FilePath

getAPIInstructorAssignmentsR :: Text -> Text -> Handler Value
getAPIInstructorAssignmentsR ident coursetitle = do 
             Entity cid _ <- canAccessClass ident coursetitle
             assignments <- runDB $ selectList [AssignmentMetadataCourse ==. cid] []
             returnJson assignments

postAPIInstructorAssignmentsR :: Text -> Text -> Handler Value
postAPIInstructorAssignmentsR ident coursetitle = do 
             (Entity cid course, mcoInst) <- roleInClass ident coursetitle
             time <- liftIO $ getCurrentTime
             val <- requireCheckJsonBody :: Handler Value
             val' <- case val of
                         Object hm ->
                             let Just tz = tzByName . courseTimeZone $ course
                                 hm' = HM.insert "date" (toJSON time) 
                                     . HM.insert "assigner" (toJSON $ maybe Nothing (Just . entityKey) mcoInst)
                                     . HM.insert "course" (toJSON cid)
                                     . HM.adjust (handleDate tz) "duedate"
                                     . HM.adjust (handleDate tz) "visibleTill"
                                     . HM.adjust (handleDate tz) "visibleFrom"
                                     . HM.adjust (handleDate tz) "gradeRelease" $ hm
                             in return $ Object hm'
                         _ -> sendStatusJSON badRequest400 ("Improper JSON" :: Text)
             case fromJSON val' :: Result AssignmentMetadata of
                   Error e -> (sendStatusJSON badRequest400 e)
                   Success asgn -> do
                       Entity uid _ <- userFromIdent ident
                       inserted <- runDB $ do
                                   let bailout = sendStatusJSON badRequest400 ("You don't have access to that document" :: Text)
                                   doc <- get (assignmentMetadataDocument asgn) >>= maybe bailout pure
                                   if documentCreator doc == uid then return () else bailout
                                   insertUnique asgn >>=
                                       maybe (sendStatusJSON conflict409 ("An assignment with that title or document already exists." :: Text)) return
                       render <- getUrlRender
                       addHeader "Location" (render $ APIInstructorAssignmentR ident coursetitle inserted)
                       sendStatusJSON created201 inserted
    where handleDate tz (String t) = 
              case parseTimeM True defaultTimeLocale "%Y-%m-%d %R" (unpack t) of
                   Just localTime -> toJSON $ localTimeToUTCTZ tz localTime
                   Nothing -> case parseTimeM True defaultTimeLocale "%Y-%m-%d" (unpack t) of
                        Just day -> toJSON $ localTimeToUTCTZ tz (LocalTime day (TimeOfDay 23 59 59))
                        Nothing -> String t
          handleDate _ o = o

getAPIInstructorAssignmentR :: Text -> Text -> AssignmentMetadataId -> Handler Value
getAPIInstructorAssignmentR ident coursetitle asid = do 
             Entity cid _ <- canAccessClass ident coursetitle
             assignment <- runDB $ assignmentPartOf asid cid
             returnJson assignment

data AssignmentPatch = AssignmentPatch
                       { patchGradeRelease :: Maybe (Maybe String)
                       , patchTotalProblems :: Maybe (Maybe Int)
                       , patchVisibleFrom :: Maybe (Maybe String)
                       , patchVisibleTill :: Maybe (Maybe String)
                       , patchDuedate :: Maybe (Maybe String)
                       , patchDescription :: Maybe (Maybe Text)
                       , patchAvailability :: Maybe (Maybe AvailabilityStatus)
                       , patchPointValue :: Maybe (Maybe Int)
                       , patchTitle :: Maybe Text
                       }

instance FromJSON AssignmentPatch where
    parseJSON = withObject "assignmentPatch" $ \o-> do
            patchGradeRelease <- o .:! "gradeRelease"
            patchTotalProblems <- o .:! "totalProblems"
            patchVisibleFrom <- o .:! "visibleFrom"
            patchVisibleTill <- o .:! "visibleTill"
            patchDuedate <- o .:! "duedate"
            patchDescription <- o .:! "description"
            patchAvailability <- o .:! "availability"
            patchPointValue <- o .:! "pointValue"
            patchTitle <- o .:? "title"
            return $ AssignmentPatch {..}

patchAPIInstructorAssignmentR :: Text -> Text -> AssignmentMetadataId -> Handler Value
patchAPIInstructorAssignmentR ident coursetitle asid = do 
             Entity cid course <- canAccessClass ident coursetitle
             patch <- requireCheckJsonBody :: Handler AssignmentPatch
             let Just tz = tzByName . courseTimeZone $ course
             asgn' <- runDB $ do assignmentPartOf asid cid
                                 updateGet asid $ concat
                                    [ maybeUpdateTime tz AssignmentMetadataGradeRelease (patchGradeRelease patch)
                                    , maybeUpdateTime tz AssignmentMetadataVisibleFrom (patchVisibleFrom patch)
                                    , maybeUpdateTime tz AssignmentMetadataVisibleTill (patchVisibleTill patch)
                                    , maybeUpdateTime tz AssignmentMetadataDuedate (patchDuedate patch)
                                    , maybeUpdate AssignmentMetadataTotalProblems (patchTotalProblems patch)
                                    , maybeUpdate AssignmentMetadataDescription (patchDescription patch)
                                    , maybeUpdate AssignmentMetadataAvailability (patchAvailability patch)
                                    , maybeUpdate AssignmentMetadataPointValue (patchPointValue patch)
                                    , maybeUpdate AssignmentMetadataTitle (patchTitle patch)
                                    ]
             returnJson asgn'
    where maybeUpdate field (Just val) = [field =. val]
          maybeUpdate _ Nothing = []

          maybeUpdateTime tz field (Just (Just s)) = 
            case handleDate tz s of
                Nothing -> []
                date -> [field =. date]
          maybeUpdateTime _ field (Just Nothing) = [field =. Nothing]
          maybeUpdateTime _ _ Nothing = []

          handleDate tz s = 
            case parseTimeM True defaultTimeLocale "%Y-%m-%d %R" s of
                   Just localTime -> Just $ localTimeToUTCTZ tz localTime
                   Nothing -> case parseTimeM True defaultTimeLocale "%Y-%m-%d" s of
                        Just day -> Just $ localTimeToUTCTZ tz (LocalTime day (TimeOfDay 23 59 59))
                        Nothing -> case parseTimeM True defaultTimeLocale "%Y-%m-%dT%T%Q%Z" s of
                               Just utc -> Just utc
                               Nothing -> Nothing
          
getAPIInstructorSubmissionsR :: Text -> Text -> Handler Value
getAPIInstructorSubmissionsR ident coursetitle = do 
             Entity cid _ <- canAccessClass ident coursetitle
             students <- runDB $ selectList [UserDataEnrolledIn ==. Just cid] []
             subs <- runDB $ forM students $ \(Entity _ ud) -> do 
                        selectList [ProblemSubmissionUserId ==. userDataUserId ud] []
             returnJson (concat subs)

getAPIInstructorAssignmentSubmissionsR :: Text -> Text -> AssignmentMetadataId -> Handler Value
getAPIInstructorAssignmentSubmissionsR ident coursetitle asid = do 
             Entity cid _ <- canAccessClass ident coursetitle
             subs <- runDB $ do assignmentPartOf asid cid
                                selectList [ProblemSubmissionAssignmentId ==. Just asid] []
             returnJson subs

getAPIInstructorAssignmentSubmissionsByStudentR :: Text -> Text -> AssignmentMetadataId -> UserDataId -> Handler Value
getAPIInstructorAssignmentSubmissionsByStudentR ident coursetitle asid udid = do 
             Entity cid _ <- canAccessClass ident coursetitle
             subs <- runDB $ do assignmentPartOf asid cid
                                ud <- get udid >>= maybe (sendStatusJSON notFound404 ("No userdata for this ident" :: Text)) pure
                                selectList [ProblemSubmissionAssignmentId ==. Just asid, ProblemSubmissionUserId ==. userDataUserId ud] []
             returnJson subs
