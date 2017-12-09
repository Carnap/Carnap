module Util.Data where

import ClassyPrelude.Yesod
import Data.List ((!!), elemIndex)
import Data.Time
import qualified Data.Map as M (fromList)

newtype BookAssignmentTable = BookAssignmentTable {readAssignmentTable :: IntMap UTCTime}
    deriving (Show, Read, Eq)
derivePersistField "BookAssignmentTable"

toTime :: String -> UTCTime
toTime = parseTimeOrError True defaultTimeLocale "%l:%M %P %Z, %b %e, %Y"

