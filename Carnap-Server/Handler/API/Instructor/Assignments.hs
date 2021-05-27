module Handler.API.Instructor.Assignments where

import           Data.Aeson
import           Import
import           Util.Data           (SharingScope (..))
import           Util.Handler
import           Util.Database (problemQuery)
import           System.Directory
import           System.FilePath

getAPIInstructorAssignmentsR :: Text -> Text -> Handler Value
getAPIInstructorAssignmentsR ident coursetitle = do 
             Entity cid _ <- canAccessClass ident coursetitle
             assignments <- runDB $ selectList [AssignmentMetadataCourse ==. cid] []
             returnJson assignments

getAPIInstructorAssignmentR :: Text -> Text -> AssignmentMetadataId -> Handler Value
getAPIInstructorAssignmentR ident coursetitle asid = do 
             Entity cid _ <- canAccessClass ident coursetitle
             assignment <- runDB $ assignmentPartOf asid cid
             returnJson assignment

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

assignmentPartOf :: (YesodPersist site, YesodPersistBackend site ~ SqlBackend) => AssignmentMetadataId -> CourseId -> YesodDB site AssignmentMetadata
assignmentPartOf asid cid = do 
        as <- get asid >>= maybe (sendStatusJSON notFound404 ("No such assignment" :: Text)) pure
        if assignmentMetadataCourse as == cid then return () else sendStatusJSON notFound404 ("No such assignment" :: Text)
        return as
