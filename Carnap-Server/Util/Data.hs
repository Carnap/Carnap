module Util.Data where

import ClassyPrelude.Yesod

data CourseEnrollment = KSUSymbolicI2016 | Birmingham2017
      deriving (Show,Read,Eq)
derivePersistField "CourseEnrollment"


data ProblemSource = CarnapTextbook | BirminghamAssignment2017
      deriving (Show,Read,Eq)
derivePersistField "ProblemSource"

class Course c where
        pointsOf :: c -> Int
        sourceOf :: c -> ProblemSource

instance Course CourseEnrollment where
        pointsOf KSUSymbolicI2016 = 725
        pointsOf Birmingham2017 = 0

        sourceOf KSUSymbolicI2016 = CarnapTextbook
        sourceOf Birmingham2017 = BirminghamAssignment2017
