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
    | TyCustomBookLink
    -- ^ custom document based book url that's used for non logged in users
    deriving (Show, Read, Eq, Enum)

data RTSetting =
      DisableGoogleReg Bool
    | InstanceAdminEmail Text
    | CustomBookLink Text
    deriving (Show, Eq)

rtSettingType :: RTSetting -> RTSetType
rtSettingType (DisableGoogleReg _) = TyDisableGoogleReg
rtSettingType (InstanceAdminEmail _) = TyInstanceAdminEmail
rtSettingType (CustomBookLink _) = TyCustomBookLink

handleResult :: Result a -> Maybe a
handleResult (Error _) = Nothing
handleResult (Success a) = Just a

parseRTSetting :: RTSetType -> Value -> Maybe RTSetting
parseRTSetting TyDisableGoogleReg val =
    DisableGoogleReg <$> handleResult (fromJSON val)
parseRTSetting TyInstanceAdminEmail val =
    InstanceAdminEmail <$> handleResult (fromJSON val)
parseRTSetting TyCustomBookLink val =
    CustomBookLink <$> handleResult (fromJSON val)

serializeRTSetting :: RTSetting -> Value
serializeRTSetting (DisableGoogleReg b) = toJSON b
serializeRTSetting (InstanceAdminEmail b) = toJSON b
serializeRTSetting (CustomBookLink l) = toJSON l

displayRTSetType :: RTSetType -> Text
displayRTSetType TyDisableGoogleReg = "Disable Google Registration"
displayRTSetType TyInstanceAdminEmail = "Administrator Email"
displayRTSetType TyCustomBookLink = "Custom Book Path (e.g. \"shared/someone@example.com/somedoc.pandoc\")"

derivePersistField "RTSetType"
