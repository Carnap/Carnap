module Settings.Runtime (
    module Settings.RuntimeDefs,
    getDisableGoogleReg,
    setDisableGoogleReg
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

setSetting :: PersistentSite site => RTSetting -> YesodDB site ()
setSetting set = do
    let ser = serializeRtSetting set
    _ <- upsert (RuntimeSetting (rtSettingType set) ser) [RuntimeSettingValue =. ser]
    return ()

withDefault :: Functor f => a -> MaybeT f a -> f a
withDefault def comp = maybe def id <$> (runMaybeT comp)

getDisableGoogleReg :: PersistentSite site => YesodDB site Bool
getDisableGoogleReg = withDefault False $ do
    DisableGoogleReg v <- getSetting TyDisableGoogleReg
    return v

setDisableGoogleReg :: PersistentSite site => Bool -> YesodDB site ()
setDisableGoogleReg val = setSetting (DisableGoogleReg val)
