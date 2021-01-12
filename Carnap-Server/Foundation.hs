module Foundation where

import Database.Persist.Sql        (ConnectionPool, runSqlPool)
import Import.NoFoundation
import Text.Hamlet                 (hamletFile)
import Yesod.Auth.OAuth2.Google
import Yesod.Auth.OAuth2 (getUserResponseJSON)
import Yesod.Auth.Dummy            (authDummy)
import qualified Yesod.Core.Unsafe as Unsafe
import Yesod.Core.Types            (Logger)
import Yesod.Form.Jquery
import Yesod.Default.Util          (addStaticContentExternal)
import TH.RelativePaths            (pathRelativeToCabalPackage)
--import Util.Database
import qualified Data.CaseInsensitive as CI
import qualified Data.Text as T
import qualified Control.Monad.Trans.Except as E
import qualified Data.Text.Encoding as TE
import qualified Data.HashMap.Strict as HM
import qualified Data.Text.Encoding.Error as TEE
import qualified Network.Wai as W
import Yesod.Auth.LTI13 (authLTI13WithWidget, PlatformInfo(..), YesodAuthLTI13(..))
import Data.Time (NominalDiffTime)
import Data.Time.Clock (addUTCTime)
import Web.Cookie (sameSiteNone, SetCookie(setCookieSameSite))

import Util.LTI

-- | The foundation datatype for your application. This can be a good place to
-- keep settings and values requiring initialization before your application
-- starts running, such as database connections. Every handler will have
-- access to the data present here.
data App = App
    { appSettings          :: AppSettings
    , appStatic            :: Static -- ^ Settings for static file serving.
    , appConnPool          :: ConnectionPool -- ^ Database connection pool.
    , appHttpManager       :: Manager
    , appLogger            :: Logger
    }

-- This is where we define all of the routes in our application. For a full
-- explanation of the syntax, please see:
-- http://www.yesodweb.com/book/routing-and-handlers
--
-- Note that this is really half the story; in Application.hs, mkYesodDispatch
-- generates the rest of the code. Please see the following documentation
-- for an explanation for this split:
-- http://www.yesodweb.com/book/scaffolding-and-the-site-template#scaffolding-and-the-site-template_foundation_and_application_modules
--
-- This function also generates the following type synonyms:
-- type Handler = HandlerT App IO
-- type Widget = WidgetT App IO ()
mkYesodData "App" $(parseRoutesFile =<< pathRelativeToCabalPackage "config/routes")

-- | A convenient synonym for creating forms.
type Form x = Html -> MForm (HandlerFor App) (FormResult x, Widget)

-- | Allows sessions to be started cross-site
crossSiteSessions :: IO (Maybe SessionBackend) -> IO (Maybe SessionBackend)
crossSiteSessions = (fmap . fmap . fmap) secureSessionCookies sslOnlySessions
    where
        sameSite cookie = cookie { setCookieSameSite = Just sameSiteNone }
        secureSessionCookies = customizeSessionCookies sameSite

-- Please see the documentation for the Yesod typeclass. There are a number
-- of settings which can be configured by overriding methods here.
instance Yesod App where
    -- Controls the base of generated URLs. For more information on modifying,
    -- see: https://github.com/yesodweb/yesod/wiki/Overriding-approot
    approot = ApprootMaster $ appRoot . appSettings

    -- Store session data on the client in encrypted cookies,
    -- default session idle timeout is 120 minutes
    --
    -- Set crossSiteSessions, allowing LTI in iframes, only if our approot is secure.
    makeSessionBackend app = (onlyIfHttps crossSiteSessions)
        $ Just <$> defaultClientSessionBackend
            120    -- timeout in minutes
            ((appDataRoot $ appSettings app) </> "client_session_key.aes")
        where isHttps = "https" `T.isPrefixOf` (appRoot $ appSettings app)
              onlyIfHttps f = if isHttps then f else id

    -- Yesod Middleware allows you to run code before and after each handler function.
    -- The defaultYesodMiddleware adds the response header "Vary: Accept, Accept-Language" and performs authorization checks.
    -- Some users may also want to add the defaultCsrfMiddleware, which:
    --   a) Sets a cookie with a CSRF token in it.
    --   b) Validates that incoming write requests include that token in either a header or POST parameter.
    -- For details, see the CSRF documentation in the Yesod.Core.Handler module of the yesod-core package.
    yesodMiddleware = defaultYesodMiddleware

    defaultLayout widget = do
        master <- getYesod
        mmsg <- getMessage

        -- We break up the default layout into two components:
        -- default-layout is the contents of the body tag, and
        -- default-layout-wrapper is the entire page. Since the final
        -- value passed to hamletToRepHtml cannot be a widget, this allows
        -- you to use normal widget features in default-layout.
        authmaybe <- maybeAuth
        (isInstructor, mdoc, mcourse) <- case authmaybe of
            Nothing -> return (False, Nothing, Nothing)
            Just uid -> runDB $ do
                mud <- getBy $ UniqueUserData $ entityKey uid
                mcour <- maybe (return Nothing) get (mud >>= userDataEnrolledIn . entityVal)
                masgn <- maybe (return Nothing) get (mcour >>= courseTextBook)
                mdoc <- maybe (return Nothing) get (assignmentMetadataDocument <$> masgn)
                return (not $ null (mud >>= userDataInstructorId . entityVal), mdoc, mcour)
        pc <- widgetToPageContent $ do
            addStylesheet $ StaticR css_bootstrap_css
            addStylesheet $ StaticR css_font_awesome_css
            $(widgetFile "default-layout")
        withUrlRenderer $(hamletFile =<< pathRelativeToCabalPackage "templates/default-layout-wrapper.hamlet")


    -- The page to be redirected to when authentication is required.
    authRoute _ = Just $ AuthR LoginR

    urlParamRenderOverride app (StaticR s) _ = case appStaticRoot $ appSettings app of
        Nothing -> Nothing
        Just r -> Just $ uncurry (joinPath app r) $ renderRoute s
    urlParamRenderOverride _ _ _ = Nothing

    -- Routes requiring authentication.
    isAuthorized route _ = case route of
         (UserR ident) -> userOrInstructorOf ident
         (RegisterR ident) -> userOrInstructorOf ident
         (RegisterEnrollR _ ident) -> userOrInstructorOf ident
         (InstructorR ident) -> instructor ident
         (InstructorQueryR ident) -> instructor ident
         (ReviewR coursetitle _) -> coinstructorOrInstructor coursetitle
         (CourseAssignmentR coursetitle _) -> enrolledIn coursetitle
         AdminR -> admin
         AdminPromoteR -> noAdmins
         _ -> return Authorized
        where retrieveInstructors cid course = runDB $ do
                     coInstructors <- map entityVal <$> selectList [CoInstructorCourse ==. cid] []
                     selectList ([UserDataInstructorId ==. Just (courseInstructor course)]
                                ||. [UserDataInstructorId <-. map (Just . coInstructorIdent) coInstructors]) []
              userOrInstructorOf ident =
                do Entity uid' user <- requireAuth
                   Entity uid _ <- runDB (getBy $ UniqueUser ident) >>= maybe notFound return
                   let ident' = userIdent user
                   mudata <- runDB $ getBy (UniqueUserData uid)
                   if ident == ident' 
                       then return Authorized
                       else do mudata' <- runDB $ getBy (UniqueUserData uid')
                               let mudv = entityVal <$> mudata
                                   mudv' = entityVal <$> mudata'
                                   mcid = mudv >>= userDataEnrolledIn
                                   miid' = mudv' >>= userDataInstructorId
                               case (mcid, miid') of
                                    _ | (userDataIsAdmin <$> mudv') == Just True -> return Authorized
                                    (Just cid, Just iid') -> do
                                       mcourse <- runDB $ get cid
                                       case courseInstructor <$> mcourse of
                                           Just iid | iid' == iid -> return Authorized
                                           _ -> (runDB $ getBy $ UniqueCoInstructor iid' cid) 
                                                >>= return . maybe (Unauthorized "It appears you're not authorized to access this page") (const Authorized)
                                    _ -> return $ Unauthorized "It appears you're not authorized to access this page"
              instructor ident =
                 do Entity uid user <- requireAuth
                    let ident' = userIdent user
                    mud <- runDB $ getBy $ UniqueUserData uid
                    let isInstructor = not $ null (mud >>= userDataInstructorId . entityVal)
                    userIsAdmin <- isAdmin uid
                    return $ if (isInstructor && ident' == ident) || userIsAdmin
                             then Authorized
                             else Unauthorized "It appears you're not authorized to access this page"
              enrolledIn coursetitle =
                  --this is the route to assignments accessible by students
                  --for a given course and to instructors
                  do uid  <- requireAuthId
                     mcourse <- runDB $ getBy (UniqueCourse coursetitle)
                     Entity cid course <- case mcourse of Just c -> return c; _ -> setMessage "no course with that title" >> notFound
                     mudata <- runDB $ getBy (UniqueUserData uid)
                     let userIsAdmin = maybe False (userDataIsAdmin . entityVal) mudata
                     instructors <- retrieveInstructors cid course
                     return $ if uid `elem` map (userDataUserId . entityVal) instructors
                                 || maybe False
                                          (\udata -> userDataEnrolledIn (entityVal udata) == Just cid)
                                          mudata
                                 || userIsAdmin
                              then Authorized
                              else Unauthorized $ "It appears you're not authorized to access this page. " ++
                                                  "For access, you need to enroll in the course \"" ++ coursetitle ++
                                                  "\". Is this the course you should be enrolled in?"
              coinstructorOrInstructor coursetitle =
                  --this is the route to the review area for a given course and
                  --assignment, and is for instructors only.
                  do uid <- requireAuthId
                     mcourse <- runDB $ getBy (UniqueCourse coursetitle)
                     Entity cid course <- case mcourse of Just c -> return c; _ -> setMessage "no course with that title" >> notFound
                     instructors <- retrieveInstructors cid course
                     userIsAdmin <- isAdmin uid
                     return $ if uid `elem` map (userDataUserId . entityVal) instructors
                                 || userIsAdmin
                              then Authorized
                              else Unauthorized "It appears you're not authorized to access this page"
              admin = do Entity uid _ <- requireAuth
                         userIsAdmin <- isAdmin uid
                         return $ if userIsAdmin
                                  then Authorized
                                  else Unauthorized "Only site administrators may access this page"
              -- only allow promoting the user if there are no other site administrators
              -- otherwise they can add other admins on /master_admin
              noAdmins =
                  do _ <- requireAuthId
                     adminCount <- runDB $ count [UserDataIsAdmin ==. True]
                     return $ if adminCount == 0
                              then Authorized
                              else Unauthorized "There are already site administrators on this site"
              isAdmin uid = runDB $ do
                  res <- getBy $ UniqueUserData uid
                  return $ maybe False (userDataIsAdmin . entityVal) res

    -- This function creates static content files in the static folder
    -- and names them based on a hash of their content. This allows
    -- expiration dates to be set far in the future without worry of
    -- users receiving stale content.
    addStaticContent ext mime content = do
        master <- getYesod
        let staticDir = appStaticDir $ appSettings master
        addStaticContentExternal
            Right
            genFileName
            staticDir
            (StaticR . flip StaticRoute [])
            ext
            mime
            content
      where
        -- Generate a unique filename based on the content itself
        genFileName lbs = "autogen-" ++ base64md5 lbs

    -- What messages should be logged. The following includes all messages when
    -- in development, and warnings and errors in production.
    shouldLogIO app _source level = return $
        appShouldLogAll (appSettings app)
            || level == LevelWarn
            || level == LevelError

    makeLogger = return . appLogger

    errorHandler (InternalError e) = do
        $logErrorS "yesod-core" e
        selectRep $ do
            provideRep $ defaultLayout $ do
                setTitle "Internal Server Error"
                [whamlet|
                    <div.container>
                     <h1>Internal Server Error
                     <p>Something has gone wrong on the server. The error is:
                     <pre>#{e}
                     <p>
                        \ If you have time, please consider submitting an error report to
                        \ <a href="mailto:gleachkr@ksu.edu?subject=server error">gleachkr@ksu.edu</a>,
                        \ containing the error message above and
                        \ a description of how the error occured including,
                        \ if possible, how to reproduce it.
                |]
            provideRep $ return $ object ["message" .= ("Internal Server Error" :: Text), "error" .= e]
    errorHandler NotFound = selectRep $ do
        provideRep $ defaultLayout $ do
            r <- waiRequest
            let path' = TE.decodeUtf8With TEE.lenientDecode $ W.rawPathInfo r
            setTitle "Not Found"
            toWidget [hamlet|
                <div.container>
                    <h1>Not Found
                    <p>The resource requested at the path:
                    <pre>#{path'}
                    <p>could not be found.
            |]
        provideRep $ return $ object ["message" .= ("Not Found" :: Text)]
    errorHandler (PermissionDenied msg) = selectRep $ do
        provideRep $ defaultLayout $ do
            setTitle "Permission Denied"
            toWidget [hamlet|
                <div.container>
                     <h1>Permission denied
                     <p>#{msg}
             |]
        provideRep $
            return $ object $ ["message" .= ("Permission Denied. " <> msg)]

    errorHandler other = defaultErrorHandler other

instance YesodJquery App where
        urlJqueryJs _ = Right "https://cdnjs.cloudflare.com/ajax/libs/jquery/3.2.1/jquery.min.js"
        urlJqueryUiJs _ = Right "https://cdnjs.cloudflare.com/ajax/libs/jqueryui/1.12.1/jquery-ui.min.js"

-- How to run database actions.
instance YesodPersist App where
    type YesodPersistBackend App = SqlBackend
    runDB action = do
        master <- getYesod
        runSqlPool action $ appConnPool master

instance YesodPersistRunner App where
    getDBRunner = defaultGetDBRunner appConnPool

instance YesodAuthLTI13 App where
    retrieveOrInsertJwks new = liftHandler $ runDB $ do
        -- maybe not thread safe but this process happens only once
        jwks <- (selectList ([]::[Filter AuthJwk]) [])
        if jwks == []
            then do
                new' <- liftIO new
                insert_ $ AuthJwk new'
                return new'
            else do
                let (Entity _ jwk1):rest = jwks
                when (rest /= []) ($logWarn "we should not have multiple jwk blobs in our database but we do!")
                return $ authJwkValue jwk1

    checkSeenNonce nonce = liftHandler $ runDB $ do
            now <- liftIO $ getCurrentTime
            deleteOld now
            rec <- getBy $ UniqueNonce nonce
            case rec of
                Nothing -> do
                    insert_ $ AuthNonce nonce now
                    return False
                Just _ -> return True
        where
            deleteOld now = do
                let olderThan = addUTCTime deleteThreshold now
                deleteWhere [AuthNonceSeenAt <. olderThan]
            -- retain old nonces for 30 days
            deleteThreshold = (-86400 * 30) :: NominalDiffTime

    retrievePlatformInfo (issuer, maybeCid) = liftHandler $ runDB $ do
        dbPInfo <- case maybeCid of
            -- if we have a cid we can select uniquely
            Just cid ->
                get $ LtiPlatformInfoKey issuer cid
            -- if we do not, we need to assert that we only get one
            Nothing -> do
                records <- selectList [LtiPlatformInfoIssuer ==. issuer] [LimitTo 2]
                return $ do
                    guard $ length records == 1
                    let (Entity _ itm) : _ = records
                    return itm
        LtiPlatformInfo {..} <- maybe
                (permissionDenied "LTI issuer not recognized or is duplicated")
                pure
                dbPInfo
        return $ PlatformInfo {
            platformIssuer = ltiPlatformInfoIssuer
          , platformClientId = ltiPlatformInfoClientId
          , platformOidcAuthEndpoint = ltiPlatformInfoOidcAuthEndpoint
          , jwksUrl = ltiPlatformInfoJwksUrl
            }

instance YesodAuth App where
    type AuthId App = UserId

    -- Where to send a user after successful login
    loginDest _ = UserDispatchR

    -- Where to send a user after logout
    logoutDest _ = HomeR

    -- Override the above two destinations when a Referer: header is present
    redirectToReferer _ = False

    authenticate creds0 = liftHandler $ runDB $ do
        -- set a session variable ltiToken with the lti token if we have one
        when (credsPlugin creds == "lti13") $ do
            let fields = ["ltiToken", "ltiIss"]
            let maybeVals = forM fields ((flip lookup) $ credsExtra creds)
            maybe (return ())
                  (\vals -> forM_ (zip fields vals) (uncurry setSession))
                  maybeVals

        x <- getBy $ UniqueUser $ credsIdent creds
        case x of
            Just (Entity uid _) -> return $ Authenticated uid
            Nothing -> Authenticated <$> insert User
                { userIdent = credsIdent creds
                , userPassword = Nothing
                }
        -- translate identifier into email for display for Google users
        -- TODO: make a prettier display for LTI users
        where creds = fromMaybe creds0 $ do
                          guard $ credsPlugin creds0 == "google"
                          Object o <- either (const Nothing) Just (getUserResponseJSON creds0)
                          String email <- HM.lookup "email" o
                          Just creds0 { credsIdent = email }

    --can't do a straight redirect, since this takes place before logout is
    --completed. Instead, we delete the credentials and the ultDestKey
    --(which is generated when we get sent to Auth, I think) and then
    --redirect manually.
    onLogout = deleteSession credsKey >> deleteSession "_ULT" >> redirect HomeR

    onLogin = liftHandler $ do
          mid <- maybeAuthId
          -- if there is an auth id, go to registration, otherwise do nothing
          traverse_ checkUserData mid

    -- appDevel is a custom method added to the settings, which is true
    -- when yesod is running in the development environment and false
    -- otherwise
    authPlugins app = let settings = appSettings app in
                          if appDevel settings
                              then [ authDummy, lti13 ]
                              else [ oauth2GoogleScoped ["email","profile"] (appKey settings) (appSecret settings),
                                     lti13 ]
        where
            lti13 = authLTI13WithWidget (\_ -> fromString "")

    authLayout widget = liftHandler $ do
        master <- getYesod
        mmsg <- getMessage
        pc <- widgetToPageContent $ do
            addStylesheet $ StaticR css_bootstrap_css
            $(widgetFile "auth-layout")
        withUrlRenderer $(hamletFile =<< pathRelativeToCabalPackage "templates/default-layout-wrapper.hamlet")

instance YesodAuthPersist App

-- This instance is required to use forms. You can modify renderMessage to
-- achieve customized and internationalized form validation messages.
instance RenderMessage App FormMessage where
    renderMessage _ _ = defaultFormMessage

-- Useful when writing code that is re-usable outside of the Handler context.
-- An example is background jobs that send email.
-- This can also be useful for writing code that works across multiple Yesod applications.
instance HasHttpManager App where
    getHttpManager = appHttpManager

unsafeHandler :: App -> Handler a -> IO a
unsafeHandler = Unsafe.fakeHandlerGetLogger appLogger

-- | given a UserId, return the userdata or redirect to
-- registration
checkUserData :: Key User -> HandlerFor App UserData
checkUserData uid = do maybeData <- runDB $ getBy $ UniqueUserData uid
                       muser <- runDB $ get uid
                       case muser of
                           Nothing -> do setMessage "no user found"
                                         redirect HomeR
                           Just u -> case maybeData of
                              -- LTI users will hit autoregistration every time
                              -- to make sure their data gets immmediately
                              -- propagated from LMS in case of e.g. name change
                              Just (Entity _ userdata) | not . userDataIsLti $ userdata
                                -> return userdata
                              _ -> doRegister u
    where
        doRegister u = do
            result <- E.runExceptT $ tryLTIAutoRegistration uid
            case result of
                Left err ->
                    do  -- show the message about auto reg if any
                        traverse_ setMessage (regErrorToString err)
                        -- if they followed a reg link, apply that
                        menroll <- lookupSession "enrolling-in"
                        redirect $ maybe
                            (RegisterR $ userIdent u)
                            ((flip RegisterEnrollR) $ userIdent u)
                            menroll
                Right ud -> return ud
