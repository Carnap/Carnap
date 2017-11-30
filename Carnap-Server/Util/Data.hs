module Util.Data where

import ClassyPrelude.Yesod
import Data.List ((!!), elemIndex)
import Data.Time
import qualified Data.Map as M (fromList)

--data Instructor = GrahamLeachKrouse 
--                | SalvatoreFlorio
--                | CharlesPence
--                | DavidSanson
--                | KeshavSingh
--    deriving (Show,Read,Eq,Enum,Bounded)

--data InstructorMetadataOld = InstructorMetadataOld
--    { instructorEmail :: Text }

--instructorData :: Instructor -> InstructorMetadataOld
--instructorData GrahamLeachKrouse = InstructorMetadataOld
--        { instructorEmail = "gleachkr@gmail.com" }
--instructorData SalvatoreFlorio = InstructorMetadataOld
--        { instructorEmail = "florio.2@buckeyemail.osu.edu" }
--instructorData CharlesPence = InstructorMetadataOld
--        { instructorEmail = "charles@charlespence.net" }
--instructorData DavidSanson = InstructorMetadataOld
--        { instructorEmail = "dsanson@gmail.com" }
--instructorData KeshavSingh = InstructorMetadataOld
--        { instructorEmail = "keshav.singh.phi@gmail.com" }

--instructorsList :: [Instructor]
--instructorsList = [minBound .. maxBound]

--instructorsDataList :: [InstructorMetadataOld]
--instructorsDataList = map instructorData instructorsList

--instructorByEmail :: Text -> Maybe Instructor
--instructorByEmail t = (!!) <$> pure instructorsList <*> elemIndex t (map instructorEmail instructorsDataList)

--data CourseEnrollment = Birmingham2017 
--                      | KSUSymbolicI2017
--                      | KSUIntroToFormal2017
--                      | KSUModalLogic2017
--                      | SandboxCourse Instructor
--      deriving (Show,Read,Eq)
--derivePersistField "CourseEnrollment"

--blankCourse instructor name = CourseMetadata
--        { pointsOf = 0
--        , sourceOf = Nothing
--        , instructorOf = instructor
--        , nameOf = name
--        , duedates = Nothing
--        }

----TODO use an enum to generate these
--regularCourseList :: [CourseEnrollment]
--regularCourseList = [Birmingham2017,KSUSymbolicI2017,KSUIntroToFormal2017,KSUModalLogic2017]

--courseList :: [CourseEnrollment]
--courseList = [Birmingham2017,KSUSymbolicI2017,KSUIntroToFormal2017,KSUModalLogic2017] ++ map SandboxCourse instructorsList


toTime :: String -> UTCTime
toTime = parseTimeOrError True defaultTimeLocale "%l:%M %P %Z, %b %e, %Y"

