module Util.Data where

import ClassyPrelude.Yesod
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Data.List ((!!), elemIndex)
import Data.Time
import Text.Read (readMaybe)
import Carnap.GHCJS.SharedTypes(ProblemSource(..),ProblemType(..),ProblemData(..), SomeRule(..))
import qualified Data.IntMap as IM (fromList)

derivePersistField "ProblemSource"

derivePersistField "ProblemType"

derivePersistField "ProblemData"

derivePersistField "SomeRule"

newtype BookAssignmentTable = BookAssignmentTable {readAssignmentTable :: IntMap UTCTime}
    deriving (Show, Read, Eq)
derivePersistField "BookAssignmentTable"

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


displayProblemData (DerivationData t _)  = t
displayProblemData (DerivationDataOpts t _ _)  = t
displayProblemData (TruthTableData t _)  = t
displayProblemData (TruthTableDataOpts t _ _) = maybe t pack ms
    where ms = (show <$> (readMaybe s :: Maybe PureForm))
               `mplus` (intercalate "," . map show <$> (readMaybe s :: Maybe [PureForm]))
               `mplus` case readMaybe s :: Maybe ([PureForm],[PureForm]) of
                                 Just (fs,gs) -> Just $ intercalate "," (map show fs) ++ " || " ++ intercalate "," (map show gs)
                                 Nothing -> Nothing
          s = unpack t
displayProblemData (TranslationData t _) = t
displayProblemData (TranslationDataOpts t _ _) = t
displayProblemData (ProblemContent t) = maybe t pack ms
    where ms = (show <$> (readMaybe s :: Maybe PureForm))
               `mplus` (intercalate "," . map show <$> (readMaybe s :: Maybe [PureForm]))
               `mplus` case readMaybe s :: Maybe ([PureForm],[PureForm]) of
                                 Just (fs,gs) -> Just $ intercalate "," (map show fs) ++ " || " ++ intercalate "," (map show gs)
                                 Nothing -> Nothing
          s = unpack t
