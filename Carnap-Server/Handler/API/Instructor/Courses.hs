module Handler.API.Instructor.Courses where

import           Data.Aeson
import           Import
import           Util.Handler

getAPIInstructorCoursesR :: Text -> Handler Value
getAPIInstructorCoursesR ident = do 
             Entity _ ud <- userDataFromIdent ident
             iid <- maybe (sendStatusJSON notFound404 ("No Instructor Data Found" :: Text)) pure (userDataInstructorId ud)
             courses <- runDB $ map entityVal <$> selectList [CourseInstructor ==. iid] []
             returnJson courses
