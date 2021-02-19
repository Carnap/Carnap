{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE NamedFieldPuns #-}
module Util.Database where

import           Carnap.GHCJS.SharedTypes (ProblemSource (..))
import           Import.NoFoundation
import           Util.API
import           Util.Data                (BookAssignmentTable)

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

maybeAPIKeyUserData
    :: PersistentSite site
    => HandlerFor site (Maybe (Entity UserData))
maybeAPIKeyUserData = unCacheMaybeUserData <$> cached (CachedMaybeUserData <$> getData)
    where getData = do mauth <- maybeAPIKey
                       case mauth of
                          Nothing -> return Nothing
                          Just (Entity _ auth) -> runDB (getBy $ UniqueUserData $ authAPIUser auth)


-- | Try to insert a piece of data into the database, returning False in
-- case of a clash
{-# DEPRECATED tryInsert "this duplicates the functionality of insertUnique and should be removed" #-}
tryInsert
    :: (PersistentSite site, PersistEntity record, PersistEntityBackend record ~ SqlBackend)
    => (record -> HandlerFor site (Maybe (Key record)))
tryInsert s = runDB $ do munique <- checkUnique s
                         case munique of
                              (Just _) -> return Nothing
                              Nothing  -> do k <- insert s
                                             return (Just k)

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
    -> HandlerFor site ()
checkCourseOwnership coursetitle = do
           mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           Entity uid _ <- requireAuth
           case mcourse of
             Nothing -> setMessage "course not found" >> notFound
             Just (Entity _cid course) -> do
               user <- runDB (get uid) >>= maybe (permissionDenied "failed to get user") pure
               classes <- classesByInstructorIdent (userIdent user)
               unless (course `elem` map entityVal classes) (permissionDenied "this doesn't appear to be your course")

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
