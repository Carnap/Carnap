module Util.Data where

import ClassyPrelude.Yesod
import Data.List ((!!), elemIndex)
import Data.Time
import Carnap.GHCJS.SharedTypes(ProblemSource(..))
import qualified Data.IntMap as IM (fromList)

derivePersistField "ProblemSource"

newtype BookAssignmentTable = BookAssignmentTable {readAssignmentTable :: IntMap UTCTime}
    deriving (Show, Read, Eq)
derivePersistField "BookAssignmentTable"

data ProblemType = Derivation | TruthTable | Translation | SyntaxCheck
    deriving (Show, Read, Eq)
derivePersistField "ProblemType"

data ProblemData = DerivationData Text Text | ProblemContent Text
    deriving (Show, Read, Eq)
derivePersistField "ProblemData"

data SharingScope = Public | InstructorsOnly | LinkOnly | Private
    deriving (Show, Read, Eq)
derivePersistField "SharingScope"

chapterOfProblemSet :: IntMap Int
chapterOfProblemSet = IM.fromList 
    [ (1,1)
    , (2,2)
    , (3,2)
    , (4,3)
    , (5,4)
    , (6,5)
    , (7,6)
    , (8,7)
    , (9,8)
    , (10,9)
    , (11,9)
    , (12,9)
    , (13,10)
    , (14,10)
    , (15,11)
    , (16,12)
    , (17,12)
    ]

toTime :: String -> UTCTime
toTime = parseTimeOrError True defaultTimeLocale "%l:%M %P %Z, %b %e, %Y"

