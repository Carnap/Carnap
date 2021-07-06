-- Defines the runtime settings. You probably don't want to import this file,
-- use Settings.Runtime instead which reexports everything from here.
module Settings.RuntimeDefs where

import           ClassyPrelude
import           Database.Persist.TH
import           Data.Aeson

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

handleResult :: Result a -> Maybe a
handleResult (Error _) = Nothing
handleResult (Success a) = Just a

parseRTSetting :: RTSetType -> Value -> Maybe RTSetting
parseRTSetting TyDisableGoogleReg val =
    DisableGoogleReg <$> handleResult (fromJSON val)
parseRTSetting TyInstanceAdminEmail val =
    InstanceAdminEmail <$> handleResult (fromJSON val)

serializeRTSetting :: RTSetting -> Value
serializeRTSetting (DisableGoogleReg b) = toJSON b
serializeRTSetting (InstanceAdminEmail b) = toJSON b

displayRTSetType :: RTSetType -> Text
displayRTSetType TyDisableGoogleReg = "Disable Google Registration"
displayRTSetType TyInstanceAdminEmail = "Administrator Email"

derivePersistField "RTSetType"
