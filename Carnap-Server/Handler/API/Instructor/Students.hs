module Handler.API.Instructor.Students where

import           Data.Aeson
import           Data.Aeson.Types
import           Data.Time
import           Data.Time.Zones
import           Data.Time.Zones.DB
import           Data.Time.Zones.All
import           Import
import           Util.Data           (SharingScope (..))
import           Util.Handler
import           Util.Database (problemQuery)
import           System.Directory
import           System.FilePath

getAPIInstructorStudentsR :: Text -> Text -> Handler Value
getAPIInstructorStudentsR ident coursetitle = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             students <- runDB $ selectList [UserDataEnrolledIn ==. Just cid] []
             returnJson students

getAPIInstructorStudentR :: Text -> Text -> UserDataId -> Handler Value
getAPIInstructorStudentR ident coursetitle udid = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             student <- runDB $ studentEnrolled udid cid
             returnJson student

getAPIInstructorStudentSubmissionsR :: Text -> Text -> UserDataId -> Handler Value
getAPIInstructorStudentSubmissionsR ident coursetitle udid = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             subs <- runDB $ do asmd <- selectList [AssignmentMetadataCourse ==. cid] []
                                ud <- studentEnrolled udid cid
                                let pq = problemQuery (userDataUserId ud) (map entityKey asmd) 
                                selectList pq []
             returnJson subs

getAPIInstructorStudentExtensionsR :: Text -> Text -> UserDataId -> Handler Value
getAPIInstructorStudentExtensionsR ident coursetitle udid = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             extensions <- runDB $ do ud <- studentEnrolled udid cid
                                      selectList [ExtensionForUser ==. userDataUserId ud] []
             returnJson extensions

postAPIInstructorStudentExtensionsR :: Text -> Text -> UserDataId -> Handler Value
postAPIInstructorStudentExtensionsR ident coursetitle udid = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             val <- requireCheckJsonBody :: Handler Value
             case parse (unpackPost course) val of
                 Error e -> sendStatusJSON badRequest400 e
                 Success (aid,until) -> do
                     Entity exid _ <- runDB $ do
                         ud <- studentEnrolled udid cid
                         assignmentPartOf aid cid --verify that the assignemnt belongs to this class
                         upsertBy (UniqueExtension aid (userDataUserId ud)) 
                                  (Extension aid (userDataUserId ud) until)
                                  [ExtensionUntil =. until]
                     returnJson exid

    where unpackPost course = withObject "post JSON" $ \o -> do
            theDate <- o .: "until" <|> dateTimeFromString o course <|> dateFromString o course
            (,) <$> o .: "onAssignment" <*> return (theDate :: UTCTime)
          dateFromString o course = do
              dateString <- o .: "until"
              day <- parseTimeM True defaultTimeLocale "%Y-%m-%d" dateString
              let Just tz = tzByName . courseTimeZone $ course
                  localTime = LocalTime day (TimeOfDay 23 59 59)
              return $ localTimeToUTCTZ tz localTime
          dateTimeFromString o course = do
              dateString <- o .: "until"
              localTime <- parseTimeM True defaultTimeLocale "%Y-%m-%d %R" dateString
              let Just tz = tzByName . courseTimeZone $ course
              return $ localTimeToUTCTZ tz localTime

getAPIInstructorStudentAccommodationsR :: Text -> Text -> UserDataId -> Handler Value
getAPIInstructorStudentAccommodationsR ident coursetitle udid = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             maccommodations <- runDB $ do ud <- studentEnrolled udid cid
                                           getBy (UniqueAccommodation cid (userDataUserId ud))
             returnJson maccommodations

getAPIInstructorStudentAssignmentTokensR :: Text -> Text -> UserDataId -> Handler Value
getAPIInstructorStudentAssignmentTokensR ident coursetitle udid = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             tokens <- runDB $ do ud <- studentEnrolled udid cid
                                  alltokens <- selectList [AssignmentAccessTokenUser ==. userDataUserId ud] []
                                  filterM (\(Entity _ tok) -> tokenCourse tok >>= \mcid -> return (mcid == Just cid)) alltokens
             returnJson tokens

deleteAPIInstructorStudentAssignmentTokenR :: Text -> Text -> UserDataId -> AssignmentAccessTokenId -> Handler Value
deleteAPIInstructorStudentAssignmentTokenR ident coursetitle udid tokid = do 
             courseEnt@(Entity cid course) <- canAccessClass ident coursetitle
             runDB $ do tok <- get tokid >>= maybe (sendStatusJSON notFound404 ("No available token for this id" :: Text)) pure
                        mcid <- tokenCourse tok
                        if mcid == Just cid 
                            then delete tokid
                            else sendStatusJSON notFound404 ("No available token for this id" :: Text)
             returnJson ("deleted token" :: Text)

studentEnrolled :: (YesodPersist site, YesodPersistBackend site ~ SqlBackend) => UserDataId -> CourseId -> YesodDB site UserData
studentEnrolled udid cid = do 
        ud <- get udid >>= maybe (sendStatusJSON notFound404 ("No userdata for this ident" :: Text)) pure
        if userDataEnrolledIn ud == Just cid then return () else sendStatusJSON notFound404 ("No userdata for this ident" :: Text)
        return ud

tokenCourse :: (YesodPersist site, YesodPersistBackend site ~ SqlBackend) => AssignmentAccessToken -> YesodDB site (Maybe CourseId)
tokenCourse tok = get (assignmentAccessTokenAssignment tok) >>= return . maybe Nothing (Just . assignmentMetadataCourse)
