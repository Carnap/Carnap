module Handler.API.Instructor.Types where
import           Data.Aeson.TH           (defaultOptions, deriveFromJSON,
                                          deriveToJSON, fieldLabelModifier)
import           Handler.API.AesonHelper
import           Import
import           Util.Data               (SharingScope)

data DocumentPost = DocumentPost
    { docPostFilename    :: Text
    , docPostDescription :: Maybe Text
    , docPostScope       :: Maybe SharingScope
    , docPostTags        :: Maybe [Text]
    }

$(deriveFromJSON
    defaultOptions
        {
            fieldLabelModifier = unPrefix "docPost"
        }
    ''DocumentPost
    )

data DocumentPatch = DocumentPatch
    { patchScope       :: Maybe SharingScope
    , patchDescription :: Maybe (Maybe Text)
    , patchTags        :: Maybe [Text]
    }

$(deriveFromJSON
    defaultOptions
        {
            fieldLabelModifier = unPrefix "patch"
        }
    ''DocumentPatch
    )

