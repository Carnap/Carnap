{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE NamedFieldPuns #-}
module Util.Database where

import           Carnap.GHCJS.SharedTypes        (ProblemSource (..))
import           Data.Aeson.TH                   (defaultOptions,
                                                  deriveFromJSON, deriveToJSON,
                                                  fieldLabelModifier)
import qualified Data.HashMap.Strict             as HM
import           Database.Esqueleto.Experimental ((:&) (..), (?.), (^.))
import qualified Database.Esqueleto.Experimental as E
import           Handler.API.AesonHelper
import           Import.NoFoundation
import           Util.API
import           Util.Data                       (BookAssignmentTable,
                                                  SharingScope)
import Control.Monad.Trans.Maybe

newtype CachedMaybeUser = CachedMaybeUser { unCacheMaybeUser :: Maybe (Entity User) }
newtype CachedMaybeUserData = CachedMaybeUserData { unCacheMaybeUserData :: Maybe (Entity UserData) }
newtype CachedMaybeUserCourse = CachedMaybeUserCourse { unCacheMaybeUserCourse :: Maybe (Entity Course) }
newtype CachedMaybeTextbook = CachedMaybeUserTextbook { unCacheMaybeUserTextbook :: Maybe (Entity AssignmentMetadata) }
newtype CachedMaybeTextbookDoc = CachedMaybeUserTextbookDoc { unCacheMaybeUserTextbookDoc :: Maybe (Entity Document) }
newtype CachedMaybeAuthAPI = CachedMaybeAuthAPI { unCacheMaybeAuthAPI :: Maybe (Entity AuthAPI) }

--retrieve userdata using a per-request cache to avoid multiple DB lookups.
maybeUserData
    :: PersistentSite site
    => HandlerFor site (Maybe (Entity UserData))
maybeUserData = unCacheMaybeUserData <$> cached (CachedMaybeUserData <$> getData)
    where getData = do authmaybe <- maybeAuth
                       case authmaybe of
                           Nothing -> return Nothing
                           Just (Entity uid _) -> runDB (getBy $ UniqueUserData uid)

--retrieve user by ident, caching to avoid multiple DB lookups
maybeUserByIdent
    :: PersistentSite site
    => Text -> HandlerFor site (Maybe (Entity User))
maybeUserByIdent ident = unCacheMaybeUser <$> cachedBy (encodeUtf8 ident) (CachedMaybeUser <$> getData)
    where getData = runDB (getBy $ UniqueUser ident)

--retrieve userdata by ident, caching to avoid multiple DB lookups
maybeUserDataByIdent
    :: PersistentSite site
    => Text -> HandlerFor site (Maybe (Entity UserData))
maybeUserDataByIdent ident = unCacheMaybeUserData <$> cachedBy (encodeUtf8 ident) (CachedMaybeUserData <$> getData)
    where getData = do ment <- maybeUserByIdent ident
                       case ment of
                           Just (Entity uid _) -> runDB (getBy $ UniqueUserData uid)
                           Nothing -> pure Nothing

maybeUserCourse
    :: PersistentSite site
    => HandlerFor site (Maybe (Entity Course))
maybeUserCourse = unCacheMaybeUserCourse <$> cached (CachedMaybeUserCourse <$> getData)
    where getData = do mud <- maybeUserData
                       case mud of
                           Nothing -> return Nothing
                           Just (Entity _ ud) -> maybe (return Nothing) (runDB . getEntity) (userDataEnrolledIn ud)

maybeUserTextbook
    :: PersistentSite site
    => HandlerFor site (Maybe (Entity AssignmentMetadata))
maybeUserTextbook = unCacheMaybeUserTextbook <$> cached (CachedMaybeUserTextbook <$> getData)
    where getData = do muc <- maybeUserCourse
                       case muc of
                           Nothing -> return Nothing
                           Just (Entity _ uc) -> maybe (return Nothing) (runDB . getEntity) (courseTextBook uc)

maybeUserTextbookDoc
    :: PersistentSite site
    => HandlerFor site (Maybe (Entity Document))
maybeUserTextbookDoc = unCacheMaybeUserTextbookDoc <$> cached (CachedMaybeUserTextbookDoc <$> getData)
    where getData = do mut <- maybeUserTextbook
                       case mut of
                           Nothing -> return Nothing
                           Just (Entity _ ut) -> runDB . getEntity $ assignmentMetadataDocument ut

maybeAPIKey
    :: PersistentSite site
    => HandlerFor site (Maybe (Entity AuthAPI))
maybeAPIKey = unCacheMaybeAuthAPI <$> cached (CachedMaybeAuthAPI <$> getData)
    where getData = do mkey <- getAPIKeyFromHeader
                       case mkey of
                           Nothing  -> return Nothing
                           Just key -> runDB $ getBy $ UniqueAuthAPI key

maybeAPIIdent
    :: (PersistentSite site)
    => HandlerFor site (Maybe Text)
maybeAPIIdent = do
    muser <- unCacheMaybeUser <$> cached (CachedMaybeUser <$> getUser)
    return $ (userIdent . entityVal) <$> muser
    where
    getUser :: PersistentSite site => HandlerFor site (Maybe (Entity User))
    getUser = do
        ak <- maybeAPIKey
        let muid = (authAPIUser . entityVal) <$> ak
        case muid of
            Nothing -> return Nothing
            Just uid -> do
                user <- (runDB $ get uid)
                return $ (Entity uid) <$> user

maybeAPIKeyUserData
    :: PersistentSite site
    => HandlerFor site (Maybe (Entity UserData))
maybeAPIKeyUserData = unCacheMaybeUserData <$> cached (CachedMaybeUserData <$> getData)
    where getData = do mauth <- maybeAPIKey
                       case mauth of
                          Nothing -> return Nothing
                          Just (Entity _ auth) -> runDB (getBy $ UniqueUserData $ authAPIUser auth)

-- | retrieve a UserId = Key User, from the user's ident.
fromIdent
    :: PersistentSite site
    => Text
    -> HandlerFor site (Key User)
fromIdent ident = do mident <- runDB (getBy $ UniqueUser ident)
                     case mident of
                        Nothing -> setMessage ("no user " ++ toHtml ident) >> notFound
                        Just (Entity k _) -> return k

-- | retrieve an ident from a UserId
getIdent
    :: PersistentSite site
    => Key User
    -> HandlerFor site (Maybe Text)
getIdent uid = (runDB $ get uid) >>= return . maybe Nothing (Just . userIdent)

checkCourseOwnership
    :: PersistentSite site
    => Text
    -> Key Course
    -> HandlerFor site ()
checkCourseOwnership ident cid = do
           classes <- classesByInstructorIdent ident
           if cid `elem` map entityKey classes
               then return ()
               else sendStatusJSON forbidden403 ("You don't have instructor access to this course" :: Text)

checkCourseOwnershipHTML
    :: PersistentSite site
    => Text
    -> Key Course
    -> HandlerFor site ()
checkCourseOwnershipHTML ident cid = do
           classes <- classesByInstructorIdent ident
           if cid `elem` map entityKey classes
               then return ()
               else permissionDenied ("You don't have instructor access to this course" :: Text)

-- | given a UserId, return Just the user data or Nothing
getUserMD
    :: PersistentSite site
    => Key User
    -> HandlerFor site (Maybe UserData)
getUserMD uid = do mmd <- runDB $ getBy $ UniqueUserData uid
                   case entityVal <$> mmd of
                       Just md -> return $ Just md
                       Nothing -> return Nothing

-- | given a CourseId, return the associated book problem sets
getProblemSets
    :: PersistentSite site
    => Key Course
    -> HandlerFor site (Maybe BookAssignmentTable)
getProblemSets cid = do mcourse <- runDB $ get cid
                        return $ mcourse >>= courseTextbookProblems

-- | class entities by instructor Ident - returns owned and co-instructed classes
classesByInstructorIdent
    :: PersistentSite site
    => Text
    -> HandlerFor site [Entity Course]
classesByInstructorIdent ident = runDB $ do
           muent <- getBy $ UniqueUser ident
           mudent <- case entityKey <$> muent of
                          Just uid -> getBy $ UniqueUserData uid
                          Nothing  -> return Nothing
           case (entityVal <$> mudent) >>= userDataInstructorId of
               Just instructordata -> do
                   owned <- selectList [CourseInstructor ==. instructordata] []
                   coInstructor <- map entityVal <$> selectList [CoInstructorIdent ==. instructordata] []
                   coOwned <- selectList [CourseId <-. (map coInstructorCourse coInstructor)] []
                   return (owned ++ coOwned)
               Nothing -> return []

-- | old derived rules by userId XXX: legacy, deprecate eventually
getDerivedRules
    :: PersistentSite site
    => Key User
    -> HandlerFor site [SavedDerivedRule]
getDerivedRules uid = runDB $ selectList [SavedDerivedRuleUserId ==. uid] []
                      >>= return . map entityVal

getRules
    :: PersistentSite site
    => Key User
    -> HandlerFor site [SavedRule]
getRules uid = runDB $ selectList [SavedRuleUserId ==. uid] []
               >>= return . map entityVal

-- | instructorId by ident
instructorIdByIdent
    :: PersistentSite site
    => Text
    -> HandlerFor site (Maybe (Key InstructorMetadata))
instructorIdByIdent ident = runDB $ do muent <- getBy $ UniqueUser ident
                                       mudent <- case entityKey <$> muent of
                                                      Just uid -> getBy $ UniqueUserData uid
                                                      Nothing -> return Nothing
                                       return $ (entityVal <$> mudent) >>= userDataInstructorId

-- | user data by InstructorId
udByInstructorId
    :: PersistentSite site
    => Key InstructorMetadata
    -> HandlerFor site (Entity UserData)
udByInstructorId id = do l <- runDB $ selectList [UserDataInstructorId ==. Just id] []
                         case l of [ud] -> return ud
                                   [] -> error $ "couldn't find any user data for instructor " ++ show id
                                   _ -> error $ "Multiple user data for instructor " ++ show id

getProblemQuery
    :: PersistentSite site
    => Key User
    -> Key Course
    -> HandlerFor site [Filter ProblemSubmission]
getProblemQuery uid cid = do asl <- runDB $ map entityKey <$> selectList [AssignmentMetadataCourse ==. cid] []
                             return $ problemQuery uid asl

problemQuery
    :: Key User
    -> [Key AssignmentMetadata]
    -> [Filter ProblemSubmission]
problemQuery uid asl = [ProblemSubmissionUserId ==. uid]
                    ++ ([ProblemSubmissionSource ==. Book] ||. [ProblemSubmissionAssignmentId <-. assignmentList])
        where assignmentList = map Just asl


data DocumentGet = DocumentGet
    { docGetId          :: DocumentId
    , docGetCreator     :: Key User
    , docGetFilename    :: Text
    , docGetDescription :: Maybe Text
    , docGetScope       :: SharingScope
    , docGetTags        :: [Text]
    , docGetDate        :: UTCTime
    } deriving (Eq)

$(deriveToJSON
    defaultOptions
        {
            fieldLabelModifier = unPrefix "docGet"
        }
    ''DocumentGet
    )

documentsWithTags
    :: (PersistentSite site)
    => UserId
    -- ^ Creator
    -> YesodDB site [DocumentGet]
documentsWithTags uid = do
    -- this query gets (document, Maybe tag) pairs for each document with each
    -- of its tags
    docsWithTags <-
        E.select $ do
            (docs :& tags) <- E.from $ E.table @Document
                `E.leftJoin` E.table @Tag
                `E.on` (\(docs :& tags) -> E.just (docs ^. DocumentId) E.==. tags ?. TagBearer)
            E.where_ (docs ^. DocumentCreator E.==. E.val uid)
            return (docs, tags)
    let
        -- we then stick the tags from each pair together for each document
        concatIdentical
            :: HM.HashMap DocumentId DocumentGet
            -> DocumentGet
            -> HM.HashMap DocumentId DocumentGet
        concatIdentical hm el =
            HM.insertWith (\old DocumentGet { docGetTags = t:_ } -> old { docGetTags = t : docGetTags old })
                (docGetId el)
                el
                hm
        toDocumentGet (Entity docId Document {..}, tag) = DocumentGet
            { docGetId = docId
            , docGetFilename = documentFilename
            , docGetDescription = documentDescription
            , docGetScope = documentScope
            , docGetTags = tagName . entityVal <$> maybeToList tag
            , docGetDate = documentDate
            }
        docs = foldl' concatIdentical HM.empty (toDocumentGet <$> docsWithTags)
    -- and finally return the stuck together ones
    return $ HM.elems docs

documentWithTags
    :: (PersistentSite site)
    => DocumentId
    -> YesodDB site (Maybe DocumentGet)
documentWithTags docid = runMaybeT $ do
    Document{..} <- MaybeT $ get docid
    tags <- lift $ selectList [TagBearer ==. docid] []
    return $ DocumentGet
        { docGetId = docid
        , docGetCreator = documentCreator
        , docGetTags = tagName . entityVal <$> tags
        , docGetFilename = documentFilename
        , docGetDate = documentDate
        , docGetScope = documentScope
        , docGetDescription = documentDescription
        }


documentsByInstructorIdent
    :: PersistentSite site
    => Text
    -> HandlerFor site [DocumentGet]
documentsByInstructorIdent ident =
    runDB $ do
        muent <- getBy $ UniqueUser ident
        case entityKey <$> muent of
            Just uid -> documentsWithTags uid
            Nothing -> return []

