module Handler.API.Instructor.Students where

import           Data.Aeson
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
                                  selectList [AssignmentAccessTokenUser ==. userDataUserId ud] []
             returnJson tokens


studentEnrolled :: (YesodPersist site, YesodPersistBackend site ~ SqlBackend) => UserDataId -> CourseId -> YesodDB site UserData
studentEnrolled udid cid = do 
        ud <- get udid >>= maybe (sendStatusJSON notFound404 ("No userdata for this ident" :: Text)) pure
        if userDataEnrolledIn ud == Just cid then return () else sendStatusJSON notFound404 ("No userdata for this ident" :: Text)
        return ud
