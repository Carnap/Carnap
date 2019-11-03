module Foundation where

import Database.Persist.Sql        (ConnectionPool, runSqlPool)
import Import.NoFoundation
import Text.Hamlet                 (hamletFile)
import Yesod.Auth.OAuth2.Google
import Yesod.Auth.OAuth2 (oauth2Url, getUserResponseJSON)
import Yesod.Auth.Dummy            (authDummy)
import qualified Yesod.Core.Unsafe as Unsafe
import Yesod.Core.Types            (Logger)
import Yesod.Form.Jquery
import Yesod.Default.Util          (addStaticContentExternal)
--import Util.Database
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import qualified Data.HashMap.Strict as HM
import qualified Data.Text.Encoding.Error as TEE
import qualified Network.Wai as W

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
mkYesodData "App" $(parseRoutesFile "config/routes")

-- | A convenient synonym for creating forms.
type Form x = Html -> MForm (HandlerT App IO) (FormResult x, Widget)

-- Please see the documentation for the Yesod typeclass. There are a number
-- of settings which can be configured by overriding methods here.
instance Yesod App where
    -- Controls the base of generated URLs. For more information on modifying,
    -- see: https://github.com/yesodweb/yesod/wiki/Overriding-approot
    approot = ApprootRequest $ \app req ->
        case appRoot $ appSettings app of
            Nothing -> getApprootText guessApproot app req
            Just root -> root

    -- Store session data on the client in encrypted cookies,
    -- default session idle timeout is 120 minutes
    makeSessionBackend _ = Just <$> defaultClientSessionBackend
        120    -- timeout in minutes
        "config/client_session_key.aes"

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
        instructors <- instructorIdentList
        pc <- widgetToPageContent $ do
            addStylesheet $ StaticR css_bootstrap_css
            addStylesheet $ StaticR css_font_awesome_css
            $(widgetFile "default-layout")
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")


    -- The page to be redirected to when authentication is required.
    authRoute app = if appDevel (appSettings app) 
                       then Just $ AuthR LoginR
                       else Just $ AuthR (oauth2Url "google")

    -- Routes requiring authentication.
    isAuthorized route _ = case route of
         (UserR ident) -> userOrInstructor ident
         (RegisterR ident) -> userOrInstructor ident
         (RegisterEnrollR _ ident) -> userOrInstructor ident
         (InstructorR ident) -> instructor ident
         (InstructorDownloadR ident _) -> instructor ident
         (ReviewR coursetitle _) -> coinstructorOrInstructor coursetitle
         (CourseAssignmentR coursetitle _) -> coinstructorOrInstructor coursetitle
         AdminR -> admin
         _ -> return Authorized
        where userOrInstructor ident = 
                do (Entity _ user) <- requireAuth
                   let ident' = userIdent user
                   instructors <- instructorIdentList
                   return $ if ident' `elem` instructors
                                --TODO Improve this to restrict to viewing your own students
                               || ident' == ident
                               || ident' == "gleachkr@gmail.com"
                            then Authorized
                            else Unauthorized "It appears you're not authorized to access this page"
              instructor ident = 
                 do (Entity _ user) <- requireAuth
                    let ident' = userIdent user
                    instructors <- instructorIdentList
                    return $ if (ident' `elem` instructors
                                && ident' == ident)
                                || ident' == "gleachkr@gmail.com"
                             then Authorized
                             else Unauthorized "It appears you're not authorized to access this page"
              coinstructorOrInstructor coursetitle = 
                  --this is the route to the review area for a given course and
                  --assignment, and is for instructors only.
                  do (Entity uid user) <- requireAuth
                     mcourse <- runDB $ getBy (UniqueCourse coursetitle)
                     course <- case mcourse of Just c -> return c; _ -> setMessage "no course with that title" >> notFound
                     coInstructors <-  runDB $ map entityVal <$> selectList [CoInstructorCourse ==. entityKey course] []
                     instructors <- runDB $ selectList ([UserDataInstructorId ==. Just (courseInstructor $ entityVal course)]
                                                       ||. [UserDataInstructorId <-. map (Just . coInstructorIdent) coInstructors]) []
                     return $ if uid `elem` map (userDataUserId . entityVal) instructors 
                                 || userIdent user == "gleachkr@gmail.com"
                              then Authorized
                              else Unauthorized "It appears you're not authorized to access this page"
              admin = do (Entity _ user) <- requireAuth
                         return $ if userIdent user == "gleachkr@gmail.com"
                                  then Authorized
                                  else Unauthorized "Only site administrators may access this page"

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

instance YesodAuth App where
    type AuthId App = UserId

    -- Where to send a user after successful login
    loginDest _ = UserDispatchR
        
    -- Where to send a user after logout
    logoutDest _ = HomeR
    
    -- Override the above two destinations when a Referer: header is present
    redirectToReferer _ = False

    authenticate creds0 = liftHandler $ runDB $ do
        x <- getBy $ UniqueUser $ credsIdent creds
        case x of
            Just (Entity uid _) -> return $ Authenticated uid
            Nothing -> Authenticated <$> insert User
                { userIdent = credsIdent creds
                , userPassword = Nothing
                }
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
          case mid of 
             Nothing -> return ()
             Just uid -> 
                 --check to see if data for this user exists
                 do maybeData <- runDB $ getBy $ UniqueUserData uid
                    case maybeData of
                        --if not, redirect to registration
                        Nothing -> 
                             do musr <- runDB $ get uid
                                menroll <- lookupSession "enrolling-in"
                                case (musr, menroll) of 
                                   (Just (User ident _), Just theclass) ->  redirect (RegisterEnrollR theclass ident)
                                   (Just (User ident _), Nothing) ->  redirect (RegisterR ident)
                                   (Nothing,_) -> return ()
                        --if so, go ahead
                        Just ud -> setMessage "Now logged in"

    -- appDevel is a custom method added to the settings, which is true
    -- when yesod is running in the development environment and false
    -- otherwise
    authPlugins app = let settings = appSettings app in 
                          if appDevel settings 
                              then [ authDummy ]
                              else [ oauth2GoogleScoped ["email","profile"] (appKey settings) (appSecret settings) ]

    authLayout widget = liftHandler $ do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        pc <- widgetToPageContent $ do
            addStylesheet $ StaticR css_bootstrap_css
            $(widgetFile "auth-layout")
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")

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

