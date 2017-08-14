module Util.Data where

import ClassyPrelude.Yesod
import Data.List ((!!), elemIndex)

data Instructor = GrahamLeachKrouse 
                | SalvatoreFlorio
                | CharlesPence
    deriving (Show,Read,Eq,Enum,Bounded)

data InstructorMetadata = InstructorMetadata
    { instructorEmail :: Text }

instructorData :: Instructor -> InstructorMetadata
instructorData GrahamLeachKrouse = InstructorMetadata
        { instructorEmail = "gleachkr@gmail.com" }
instructorData SalvatoreFlorio = InstructorMetadata
        { instructorEmail = "florio.2@buckeyemail.osu.edu" }
instructorData CharlesPence = InstructorMetadata
        { instructorEmail = "charles@charlespence.net" }

instructorsList :: [Instructor]
instructorsList = [minBound .. maxBound]

instructorsDataList :: [InstructorMetadata]
instructorsDataList = map instructorData instructorsList

instructorByEmail :: Text -> Maybe Instructor
instructorByEmail t = (!!) <$> (pure instructorsList) <*> elemIndex t (map instructorEmail instructorsDataList)

data CourseEnrollment = Birmingham2017 
                      | KSUSymbolicI2017
                      | KSUIntroToFormal2017
                      | SandboxCourse Instructor
      deriving (Show,Read,Eq)
derivePersistField "CourseEnrollment"

data CourseMetadata = CourseMetadata 
                    { pointsOf :: Int
                    , sourceOf :: Maybe ProblemSource
                    , instructorOf :: Instructor
                    , nameOf :: Text
                    }

blankCourse instructor name = CourseMetadata
        { pointsOf = 0
        , sourceOf = Nothing
        , instructorOf = instructor
        , nameOf = name
        }



courseData :: CourseEnrollment -> CourseMetadata
courseData Birmingham2017 = blankCourse SalvatoreFlorio "Logic - University of Birmingham"
courseData KSUSymbolicI2017 = (blankCourse GrahamLeachKrouse "Symbolic Logic I - Kansas State University")
    {sourceOf = Just CarnapTextbook}
courseData KSUIntroToFormal2017 = (blankCourse GrahamLeachKrouse "Introduction to Formal Logic - Kansas State University")
    {sourceOf = Just CarnapTextbook}
courseData (SandboxCourse i) = blankCourse i "Sandbox Course"

courseList :: [CourseEnrollment]
courseList = [Birmingham2017,KSUSymbolicI2017,KSUIntroToFormal2017] ++ map SandboxCourse instructorsList

coursesByInstructor :: Instructor -> [CourseEnrollment]
coursesByInstructor i = filter (\c -> instructorOf (courseData c) == i) courseList

data ProblemSource = CarnapTextbook 
                   | CourseAssignment CourseEnrollment
      deriving (Show,Read,Eq)
derivePersistField "ProblemSource"
