{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ConstraintKinds #-}
module Util.LTI (
    tryLTIAutoRegistration
  , regErrorToString
  , tripleFromDB
  , AutoregTriple(..)
) where
import Import.NoFoundation
import qualified Control.Monad.Trans.Except as E
import qualified Yesod.Auth.LTI13 as LTI
import Yesod.Auth.LTI13 (UncheckedLtiTokenClaims(..))
import Data.Aeson (encode, decodeStrict)
import qualified Data.Text as T

-- | A type class to shorten the mess required to have generic functions using
--   the database (used for modules when we cannot name the @App@ instance
--   since they are imported by Foundation where it is defined)
type PersistentSite site =
    (PersistUniqueRead (YesodPersistBackend site),
     PersistUniqueWrite (YesodPersistBackend site),
     YesodPersist site,
     BaseBackend (YesodPersistBackend site) ~ SqlBackend)


data LTIUserData
    = LTIUserData
    { firstName    :: Text
    , lastName     :: Text
    , email        :: Maybe Text
    -- ^ email given to us by the LTI system
    , universityId :: Maybe Text
    -- ^ @person_sourcedid@ of the user. Probably a student ID number.
    , ltiTriple    :: AutoregTriple
    -- ^ unique identifier of the course
    } deriving (Show)

-- | Triple of 'issuer', 'deploymentId', 'contextId' uniquely identifying a
--   course globally.
data AutoregTriple
    = AutoregTriple
    { label :: Maybe Text
    -- ^ label of the course, probably a course code
    , ltiIssuer :: Text
    -- ^ LTI issuer
    , ltiDeploymentId :: Text
    -- ^ LTI deployment id
    , ltiContextId :: Text
    -- ^ GUID/other 'deploymentId'-unique identifier for the class
    } deriving (Show, Generic)

instance ToJSON AutoregTriple
instance FromJSON AutoregTriple

data AutoregError
    = MissingContextClaim
    | MissingNameField
    | NoLtiInfo
    | LtiNotRegistered AutoregTriple
    deriving (Show)

regErrorToString :: AutoregError -> Maybe Html
regErrorToString MissingContextClaim = Just "The required `context` claim was not provided by the LTI platform."
regErrorToString MissingNameField = Just "The required `firstName` or `lastName` claim was not provided by the LTI platform."
-- this happens if the user didn't log in via LTI
regErrorToString NoLtiInfo = Nothing
regErrorToString (LtiNotRegistered tp)
    = Just [shamlet|
        <p>LTI Course not registered.
        <p>An instructor can register it by entering:
                <code> #{regInfoJson}
           in the "LTI Autoregistration ID" field in their course settings page.
        |]
    where regInfoJson = decodeUtf8 . toStrict . encode $ tp

tripleFromDB :: CourseAutoreg -> AutoregTriple
tripleFromDB (CourseAutoreg lab iss did cid _) = AutoregTriple lab iss did cid

tryLTIAutoRegistration
    :: PersistentSite site
    => Key User -> E.ExceptT AutoregError (HandlerFor site) UserData
tryLTIAutoRegistration uid = do
    sess <- lift getSession

    -- leave early if either we had no LTI data in the user token or
    -- the data is bad
    let ld = getLTIData sess
    $logDebug ("got lti data of " <> (T.pack . show $ ld))

    sd <- (E.except $ ld)
        >>= maybe (E.throwE NoLtiInfo) pure

    let LTIUserData { firstName, lastName, ltiTriple, email, universityId } = sd
        AutoregTriple { ltiContextId, ltiDeploymentId, ltiIssuer } = ltiTriple
    courseId <- (lift $ getLTICourseData ltiIssuer ltiContextId ltiDeploymentId)
            >>= maybe (E.throwE $ LtiNotRegistered ltiTriple) pure

    let udata = UserData {
          userDataFirstName = firstName
        , userDataLastName = lastName
        , userDataEmail = email
        , userDataEnrolledIn = Just courseId
        , userDataUniversityId = universityId
        , userDataInstructorId = Nothing
        , userDataIsAdmin = False
        , userDataIsLti = True
        , userDataUserId = uid
        }
    -- LTI users cannot update their own profile, so we will update it every
    -- time on launch.
    entityVal <$> (lift . runDB $ upsertBy
        (UniqueUserData uid)
        udata
        [ UserDataFirstName    =. firstName
        , UserDataLastName     =. lastName
        , UserDataEmail        =. email
        , UserDataEnrolledIn   =. Just courseId
        , UserDataUniversityId =. universityId
        , UserDataIsLti        =. True
        ])

require :: a -> Maybe b -> Either a b
require err name = maybe (Left err) Right name

getLTIData :: SessionMap -> Either AutoregError (Maybe LTIUserData)
getLTIData sess = do
    let maybeLtiTok = decodeStrict =<< lookup "ltiToken" sess
    let maybeLtiIss = decodeUtf8 <$> lookup "ltiIss" sess

    case (,) <$> maybeLtiTok <*> maybeLtiIss of
        Nothing -> Right Nothing
        Just (tok, iss) -> do
            -- this has already passed checking on login
            let UncheckedLtiTokenClaims { context, firstName, lastName, deploymentId, email, lis } = tok
            let triple = AutoregTriple
                        <$> Right (LTI.contextLabel =<< context)
                        <*> Right iss
                        <*> Right deploymentId
                        <*> (require MissingContextClaim $ LTI.contextId <$> context)

            pure . Just =<< LTIUserData
                <$> require MissingNameField firstName
                <*> require MissingNameField lastName
                <*> Right email
                <*> Right (LTI.personSourcedId =<< lis)
                <*> triple

getLTICourseData
    :: PersistentSite site
    => Text -> Text -> Text -> HandlerFor site (Maybe (Key Course))
getLTICourseData issuer contextId deploymentId = do
    autoreg <- runDB . getBy $ UniqueAutoregTriple issuer deploymentId contextId
    -- we find an autoreg record, turn it into the course ID to register in
    pure (courseAutoregCourse <$> (entityVal <$> autoreg))
