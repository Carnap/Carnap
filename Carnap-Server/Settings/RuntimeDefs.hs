-- Defines the runtime settings. You probably don't want to import this file,
-- use Settings.Runtime instead which reexports everything from here.
module Settings.RuntimeDefs where

import           ClassyPrelude
import           Database.Persist.TH
import qualified Data.Aeson as A

data RTSetType =
    TyDisableGoogleReg
    -- ^ disable new registrations of accounts with the Google login back end
    deriving (Show, Read, Eq, Enum)

data RTSetting =
    DisableGoogleReg Bool
    deriving (Show, Eq)

rtSettingType :: RTSetting -> RTSetType
rtSettingType (DisableGoogleReg _) = TyDisableGoogleReg

parseRtSetting :: RTSetType -> ByteString -> Maybe RTSetting
parseRtSetting TyDisableGoogleReg val =
    DisableGoogleReg <$> A.decodeStrict val

serializeRtSetting :: RTSetting -> ByteString
serializeRtSetting (DisableGoogleReg b) = toStrict . A.encode $ b

derivePersistField "RTSetType"
