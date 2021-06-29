-- Defines the runtime settings. You probably don't want to import this file,
-- use Settings.Runtime instead which reexports everything from here.
module Settings.RuntimeDefs where

import           ClassyPrelude
import           Database.Persist.TH
import qualified Data.Aeson as A

data RTSetType =
      TyDisableGoogleReg
    -- ^ disable new registrations of accounts with the Google login back end
    | TyInstanceAdminEmail
    -- ^ the email for the administrator of this Carnap instance
    deriving (Show, Read, Eq, Enum)

data RTSetting =
      DisableGoogleReg Bool
    | InstanceAdminEmail Text
    deriving (Show, Eq)

rtSettingType :: RTSetting -> RTSetType
rtSettingType (DisableGoogleReg _) = TyDisableGoogleReg
rtSettingType (InstanceAdminEmail _) = TyInstanceAdminEmail

parseRtSetting :: RTSetType -> ByteString -> Maybe RTSetting
parseRtSetting TyDisableGoogleReg val =
    DisableGoogleReg <$> A.decodeStrict val
parseRtSetting TyInstanceAdminEmail val =
    InstanceAdminEmail <$> A.decodeStrict val

serializeRtSetting :: RTSetting -> ByteString
serializeRtSetting (DisableGoogleReg b) = toStrict . A.encode $ b
serializeRtSetting (InstanceAdminEmail b) = toStrict . A.encode $ b

derivePersistField "RTSetType"
