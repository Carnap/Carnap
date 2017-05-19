module Util.Data where

import ClassyPrelude.Yesod
import Data.List ((!!), elemIndex)

data Instructor = GrahamLeachKrouse 
                | SalvatoreFlorio
                | CharlesPence
    deriving (Show,Read,Eq,Enum,Bounded)

data InstructorMetadata = InstructorMetadata
    { instructorEmail :: Text
    , instructorCourse :: CourseEnrollment
    }

instructorData :: Instructor -> InstructorMetadata
instructorData GrahamLeachKrouse = InstructorMetadata
        { instructorEmail = "gleachkr@gmail.com"
        , instructorCourse = KSUSymbolicI2016
        }
instructorData SalvatoreFlorio = InstructorMetadata
        { instructorEmail = "florio.2@buckeyemail.osu.edu"
        , instructorCourse = Birmingham2017
        }
instructorData CharlesPence = InstructorMetadata
        { instructorEmail = "charles@charlespence.net"
        , instructorCourse = SandboxCourse CharlesPence
        }

instructorsList :: [Instructor]
instructorsList = [minBound .. maxBound]

instructorsDataList :: [InstructorMetadata]
instructorsDataList = map instructorData instructorsList

instructorByEmail :: Text -> Maybe Instructor
instructorByEmail t = (!!) <$> (pure instructorsList) <*> elemIndex t (map instructorEmail instructorsDataList)

data CourseEnrollment = KSUSymbolicI2016 
                      | Birmingham2017 
                      | SandboxCourse Instructor
      deriving (Show,Read,Eq)
derivePersistField "CourseEnrollment"

data ProblemSource = CarnapTextbook 
                   | BirminghamAssignment2017 
                   | SandboxSource Instructor
      deriving (Show,Read,Eq)
derivePersistField "ProblemSource"

class Course c where
        pointsOf :: c -> Int
        sourceOf :: c -> ProblemSource

instance Course CourseEnrollment where
        pointsOf KSUSymbolicI2016 = 725
        pointsOf Birmingham2017 = 0
        pointsOf (SandboxCourse _) = 0

        sourceOf KSUSymbolicI2016 = CarnapTextbook
        sourceOf Birmingham2017 = BirminghamAssignment2017
        sourceOf (SandboxCourse i) = SandboxSource i
