module Util.Data where

import ClassyPrelude.Yesod
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Carnap.Languages.PureFirstOrder.Syntax (PureFOLForm)
import Data.List ((!!), elemIndex)
import Data.Time
import Text.Read (readMaybe)
import Text.Pandoc (Extension(..), extensionsFromList)
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

carnapPandocExtensions = extensionsFromList 
        [ Ext_raw_html
        , Ext_markdown_in_html_blocks
        , Ext_auto_identifiers
        , Ext_tex_math_dollars
        , Ext_fenced_code_blocks
        , Ext_backtick_code_blocks
        , Ext_line_blocks
        , Ext_fancy_lists
        , Ext_definition_lists
        , Ext_example_lists
        , Ext_simple_tables
        , Ext_multiline_tables
        , Ext_footnotes
        , Ext_fenced_code_attributes
        ]

toTime :: String -> UTCTime
toTime = parseTimeOrError True defaultTimeLocale "%l:%M %P %Z, %b %e, %Y"

displayProblemData (DerivationData t _)  = t
displayProblemData (DerivationDataOpts t _ _)  = t
displayProblemData (TruthTableData t _)  = t
displayProblemData (CounterModelDataOpts t _ _) = maybe t pack ms
    where ms = (show <$> (readMaybe s :: Maybe PureFOLForm))
               `mplus` (intercalate "," . map show <$> (readMaybe s :: Maybe [PureFOLForm]))
          s = unpack t
displayProblemData (TruthTableDataOpts t _ _) = maybe t pack ms
    where ms = (show <$> (readMaybe s :: Maybe PureForm))
               `mplus` (intercalate "," . map show <$> (readMaybe s :: Maybe [PureForm]))
               `mplus` case readMaybe s :: Maybe ([PureForm],[PureForm]) of
                                 Just (fs,gs) -> Just $ intercalate "," (map show fs) ++ " || " ++ intercalate "," (map show gs)
                                 Nothing -> Nothing
          s = unpack t
displayProblemData (TranslationData t _) = t
displayProblemData (TranslationDataOpts t _ _) = t
displayProblemData (QualitativeProblemDataOpts t _ _) = t
displayProblemData (SequentCalcData t _ _) = t
displayProblemData (ProblemContent t) = maybe t pack ms
    where ms = (show <$> (readMaybe s :: Maybe PureForm))
               `mplus` (intercalate "," . map show <$> (readMaybe s :: Maybe [PureForm]))
               `mplus` case readMaybe s :: Maybe ([PureForm],[PureForm]) of
                                 Just (fs,gs) -> Just $ intercalate "," (map show fs) ++ " || " ++ intercalate "," (map show gs)
                                 Nothing -> Nothing
               `mplus` (show <$> (readMaybe s :: Maybe PureFOLForm))
               `mplus` (intercalate "," . map show <$> (readMaybe s :: Maybe [PureFOLForm]))
          s = unpack t
