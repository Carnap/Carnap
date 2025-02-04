module Settings.Runtime (
    module Settings.RuntimeDefs,
    BookyYesod(..),
    getDisableGoogleReg,
    getInstanceAdminEmail,
    getBookLink,
    setRtSetting,
    getRtSettings,
) where

import           Control.Monad.Trans.Maybe (MaybeT (..))
import qualified Data.Text                 as T
import           Import.NoFoundation
import           Settings.RuntimeDefs

getSettingRaw :: PersistentSite site => RTSetType -> MaybeT (YesodDB site) Value
getSettingRaw ty =
    runtimeSettingValue . entityVal
        <$> MaybeT (getBy (UniqueSetting ty))

getSetting :: PersistentSite site => RTSetType -> MaybeT (YesodDB site) RTSetting
getSetting ty = do
    set <- getSettingRaw ty
    MaybeT . return $ parseRTSetting ty set

setRtSetting :: PersistentSite site => RTSetting -> YesodDB site ()
setRtSetting set = do
    let ser = serializeRTSetting set
    _ <- upsert (RuntimeSetting (rtSettingType set) ser) [RuntimeSettingValue =. ser]
    return ()

getRtSettings :: (PersistentSite site, BookyYesod site) => YesodDB site [RTSetting]
getRtSettings = do
    sequence
        [ DisableGoogleReg <$> getDisableGoogleReg
        , InstanceAdminEmail <$> getInstanceAdminEmail
        , CustomBookLink . renderBookLink <$> getBookLink
        ]
    where
    renderBookLink link =
        let (segs, _params) = renderRoute link
        in T.intercalate "/" segs

withDefault :: Functor f => a -> MaybeT f a -> f a
withDefault def comp = fromMaybe def <$> runMaybeT comp

getDisableGoogleReg :: PersistentSite site => YesodDB site Bool
getDisableGoogleReg = withDefault False $ do
    DisableGoogleReg v <- getSetting TyDisableGoogleReg
    return v

getInstanceAdminEmail :: PersistentSite site => YesodDB site Text
getInstanceAdminEmail = withDefault "gleachkr@gmail.com" $ do
    InstanceAdminEmail v <- getSetting TyInstanceAdminEmail
    return v

-- | A Yesod with a @BookR@, of course!
class (Yesod site, ParseRoute site) => BookyYesod site where
    bookRoute :: Route site

getBookLink :: (PersistentSite site, BookyYesod site) => YesodDB site (Route site)
getBookLink = withDefault bookRoute $ do
    CustomBookLink v <- getSetting TyCustomBookLink
    yesod <- lift getYesod
    cleaned <- MaybeT
        $ case cleanPath yesod (T.splitOn "/" v) of
            Right clean -> return . Just $ clean
            Left unclean      -> do
                $logWarn ("Bad book link, becomes " <> (T.pack . show $ unclean))
                return Nothing
    MaybeT . return $ parseRoute (cleaned, [])
