{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
module Util.Database where

import Import.NoFoundation
import Carnap.GHCJS.SharedTypes(ProblemSource(..))

newtype CachedMaybeUserData = CachedMaybeUserData { unCacheMaybeUserData :: Maybe (Entity UserData) }
newtype CachedMaybeUserCourse = CachedMaybeUserCourse { unCacheMaybeUserCourse :: Maybe (Entity Course) }
newtype CachedMaybeTextbook = CachedMaybeUserTextbook { unCacheMaybeUserTextbook :: Maybe (Entity AssignmentMetadata) }
newtype CachedMaybeTextbookDoc = CachedMaybeUserTextbookDoc { unCacheMaybeUserTextbookDoc :: Maybe (Entity Document) }

--retrieve userdata using a per-request cache to avoid multiple DB lookups.
maybeUserData = unCacheMaybeUserData <$> cached (CachedMaybeUserData <$> getData)
    where getData = do authmaybe <- maybeAuth
                       case authmaybe of
                           Nothing -> return Nothing
                           Just (Entity uid _) -> runDB (getBy $ UniqueUserData uid)

maybeUserCourse = unCacheMaybeUserCourse <$> cached (CachedMaybeUserCourse <$> getData)
    where getData = do mud <- maybeUserData
                       case mud of
                           Nothing -> return Nothing
                           Just (Entity _ ud) -> maybe (return Nothing) (runDB . getEntity) (userDataEnrolledIn ud)

maybeUserTextbook = unCacheMaybeUserTextbook <$> cached (CachedMaybeUserTextbook <$> getData)
    where getData = do muc <- maybeUserCourse
                       case muc of
                           Nothing -> return Nothing
                           Just (Entity _ uc) -> maybe (return Nothing) (runDB . getEntity) (courseTextBook uc)

maybeUserTextbookDoc = unCacheMaybeUserTextbookDoc <$> cached (CachedMaybeUserTextbookDoc <$> getData)
    where getData = do mut <- maybeUserTextbook
                       case mut of
                           Nothing -> return Nothing
                           Just (Entity _ ut) -> runDB . getEntity $ assignmentMetadataDocument ut
                           
-- | Try to insert a piece of data into the database, returning False in
-- case of a clash
tryInsert s = runDB $ do munique <- checkUnique s
                         case munique of
                              (Just _) -> return Nothing
                              Nothing  -> do k <- insert s
                                             return (Just k)

-- | retrieve a UserId = Key User, from the user's ident.
fromIdent ident = do mident <- runDB (getBy $ UniqueUser ident)
                     case mident of
                        Nothing -> setMessage ("no user " ++ toHtml ident) >> notFound
                        Just (Entity k _) -> return k

-- | retrieve an ident from a UserId
getIdent uid = (runDB $ get uid) >>= return . maybe Nothing (Just . userIdent)

checkCourseOwnership :: (YesodAuthPersist master,
                         PersistUniqueRead (YesodPersistBackend master),
                         PersistQueryRead (YesodPersistBackend master),
                         BaseBackend (YesodPersistBackend master) ~ SqlBackend,
                         AuthId master ~ Key User, AuthEntity master ~ User) =>
                        Text -> HandlerFor master ()
checkCourseOwnership coursetitle = do
           mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           Entity uid _ <- requireAuth
           case mcourse of
             Nothing -> setMessage "course not found" >> notFound
             Just (Entity cid course) -> do
               user <- runDB (get uid) >>= maybe (permissionDenied "failed to get user") pure
               classes <- classesByInstructorIdent (userIdent user)
               unless (course `elem` map entityVal classes) (permissionDenied "this doesn't appear to be your course")


-- | given a UserId, return Just the user data or Nothing
getUserMD uid = do mmd <- runDB $ getBy $ UniqueUserData uid
                   case entityVal <$> mmd of
                       Just md -> return $ Just md
                       Nothing -> return Nothing

-- | given a CourseId, return the associated book problem sets
getProblemSets cid = do mcourse <- runDB $ get cid
                        return $ mcourse >>= courseTextbookProblems

-- | class entities by instructor Ident - returns owned and co-instructed classes
classesByInstructorIdent ident = runDB $ do
           muent <- getBy $ UniqueUser ident
           mudent <- case entityKey <$> muent of
                          Just uid -> getBy $ UniqueUserData uid
                          Nothing -> return Nothing
           case (entityVal <$> mudent) >>= userDataInstructorId of
               Just instructordata -> do
                   owned <- selectList [CourseInstructor ==. instructordata] []
                   coInstructor <- map entityVal <$> selectList [CoInstructorIdent ==. instructordata] []
                   coOwned <- selectList [CourseId <-. (map coInstructorCourse coInstructor)] []
                   return (owned ++ coOwned)
               Nothing -> return []

documentsByInstructorIdent ident = runDB $ do muent <- getBy $ UniqueUser ident
                                              case entityKey <$> muent of
                                                  Just uid -> selectList [DocumentCreator ==. uid] []
                                                  Nothing -> return []

-- | old derived rules by userId XXX: legacy, deprecate eventually
getDerivedRules uid = runDB $ selectList [SavedDerivedRuleUserId ==. uid] []
                      >>= return . map entityVal

getRules uid = runDB $ selectList [SavedRuleUserId ==. uid] []
               >>= return . map entityVal

-- | instructorId by ident
instructorIdByIdent ident = runDB $ do muent <- getBy $ UniqueUser ident
                                       mudent <- case entityKey <$> muent of
                                                      Just uid -> getBy $ UniqueUserData uid
                                                      Nothing -> return Nothing
                                       return $ (entityVal <$> mudent) >>= userDataInstructorId

-- | user data by InstructorId
udByInstructorId id = do l <- runDB $ selectList [UserDataInstructorId ==. Just id] []
                         case l of [ud] -> return ud
                                   [] -> error $ "couldn't find any user data for instructor " ++ show id
                                   l -> error $ "Multipe user data for instructor " ++ show id

getProblemQuery uid cid = do asl <- runDB $ map entityKey <$> selectList [AssignmentMetadataCourse ==. cid] []
                             return $ problemQuery uid asl

problemQuery uid asl = [ProblemSubmissionUserId ==. uid] 
                    ++ ([ProblemSubmissionSource ==. Book] ||. [ProblemSubmissionAssignmentId <-. assignmentList])
        where assignmentList = map Just asl
