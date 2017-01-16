module Util.Data where

import ClassyPrelude.Yesod

data CourseEnrollment = KSUSymbolicI2016 | Birmingham2017
      deriving (Show,Read,Eq)
derivePersistField "CourseEnrollment"

data ProblemSource = CarnapTextbook | BirminghamAssignment2017
      deriving (Show,Read,Eq)
derivePersistField "ProblemSource"
