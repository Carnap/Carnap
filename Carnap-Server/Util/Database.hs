{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE NamedFieldPuns #-}
module Util.Database where

import           Carnap.GHCJS.SharedTypes (ProblemSource (..))
import           Import.NoFoundation
import           Util.API
import           Util.Data                (BookAssignmentTable)

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

documentsByInstructorIdent
    :: PersistentSite site
    => Text
    -> HandlerFor site [Entity Document]
documentsByInstructorIdent ident = runDB $ do muent <- getBy $ UniqueUser ident
                                              case entityKey <$> muent of
                                                  Just uid -> selectList [DocumentCreator ==. uid] []
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

