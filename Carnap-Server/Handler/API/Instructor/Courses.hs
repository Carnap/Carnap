module Handler.API.Instructor.Courses where

import           Data.Aeson
import           Data.Time
import           Data.Time.Zones
import           Data.Time.Zones.DB
import           Data.Time.Zones.All
import           Data.HashMap.Strict as HM
import           Import
import           Util.Handler

getAPIInstructorCoursesR :: Text -> Handler Value
getAPIInstructorCoursesR ident = do 
             Entity _ ud <- userDataFromIdent ident
             iid <- maybe (sendStatusJSON notFound404 ("No Instructor Data Found" :: Text)) pure (userDataInstructorId ud)
             courses <- runDB $ Import.map entityVal <$> selectList [CourseInstructor ==. iid] []
             returnJson courses
