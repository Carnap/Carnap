module Settings.Runtime (
    module Settings.RuntimeDefs,
    getDisableGoogleReg,
    getInstanceAdminEmail,
    setRtSetting,
    getRtSettings
) where

import           Control.Monad.Trans.Maybe (MaybeT (..))
import           Import.NoFoundation
import           Settings.RuntimeDefs

getSettingRaw :: PersistentSite site => RTSetType -> MaybeT (YesodDB site) ByteString
getSettingRaw ty =
    runtimeSettingValue . entityVal
        <$> (MaybeT $ getBy (UniqueSetting ty))

getSetting :: PersistentSite site => RTSetType -> MaybeT (YesodDB site) RTSetting
getSetting ty = do
    set <- getSettingRaw $ ty
    MaybeT . return $ parseRtSetting ty set

setRtSetting :: PersistentSite site => RTSetting -> YesodDB site ()
setRtSetting set = do
    let ser = serializeRtSetting set
    _ <- upsert (RuntimeSetting (rtSettingType set) ser) [RuntimeSettingValue =. ser]
    return ()

getRtSettings :: PersistentSite site => YesodDB site [RTSetting]
getRtSettings = do
    sequence
        [ DisableGoogleReg <$> getDisableGoogleReg
        , InstanceAdminEmail <$> getInstanceAdminEmail
        ]

withDefault :: Functor f => a -> MaybeT f a -> f a
withDefault def comp = fromMaybe def <$> (runMaybeT comp)

getDisableGoogleReg :: PersistentSite site => YesodDB site Bool
getDisableGoogleReg = withDefault False $ do
    DisableGoogleReg v <- getSetting TyDisableGoogleReg
    return v

getInstanceAdminEmail :: PersistentSite site => YesodDB site Text
getInstanceAdminEmail = withDefault "gleachkr@gmail.com" $ do
    InstanceAdminEmail v <- getSetting TyInstanceAdminEmail
    return v
