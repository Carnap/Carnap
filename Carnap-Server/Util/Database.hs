{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
module Util.Database where

import Import
import System.Directory (doesFileExist)
import Carnap.GHCJS.SharedTypes(ProblemSource(..))

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

-- | given an ident get the director in which assignments are stored for
-- the instructor with that ident
assignmentDir ident = do master <- getYesod
                         return $ (appDataRoot $ appSettings master) </> "documents" </> unpack ident

-- | given a filename, retrieve the associated assignment for the course
-- you're currently enrolled in and the path to the file.
getAssignment filename =
        do muid <- maybeAuthId
           ud <- case muid of
                   Nothing -> setMessage "you need to be logged in to access assignments" >> redirect HomeR
                   Just uid -> checkUserData uid
           coursent <- case userDataEnrolledIn ud of
                            Just cid -> do
                               maybeCourse <- runDB $ get cid
                               case maybeCourse of
                                  Just course -> return (Entity cid course)
                                  Nothing     -> setMessage "failed to retrieve course" >> notFound
                            Nothing -> do setMessage "you need to be enrolled in a course to access assignments"
                                          redirect HomeR
           retrieveAssignment coursent filename

getAssignmentByCourse coursetitle filename =
        do Entity uid _ <- requireAuth
           mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           case mcourse of
             Nothing -> setMessage "no class with this title" >> notFound
             Just c -> retrieveAssignment c filename

getAssignmentByOwner ident filename =
        do Entity uid _ <- requireAuth
           ud <- checkUserData uid
           uid <- fromIdent ident
           case userDataEnrolledIn ud of
             Nothing -> do setMessage "you need to be enrolled in a course to access assignments" >> redirect HomeR
             Just cid -> do
               mcourse <- runDB $ get cid
               case mcourse of
                   Nothing -> error ("no course found with cid " ++ show cid)
                   Just course -> retrieveAssignment (Entity cid course) filename

getAssignmentByCourseAndOwner coursetitle ident filename =
        do uid <- fromIdent ident
           mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           case mcourse of
             Nothing -> do setMessage "no class with this title" >> notFound
             Just c -> retrieveAssignment c filename

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

retrieveAssignment (Entity cid course) filename = do
           alldocs <- runDB $ selectList [DocumentFilename ==. filename] []
           docs <- filterM (creatorAccess cid course) alldocs
           case docs of
                [] -> setMessage ("can't find document record with filename " ++ toHtml filename) >> notFound
                docs -> do
                   let lookup (Entity k doc)= do
                            masgn <- getBy $ UniqueAssignment k cid
                            case masgn of Nothing -> return Nothing; Just asgn -> return (Just (doc,asgn))
                   asgns <- runDB $ catMaybes <$> mapM lookup docs
                   case asgns of
                      [] -> setMessage ("can't find assignment for this course with filename " ++ toHtml filename) >> notFound
                      [(doc,asgn)] -> do
                           maybeIdent <- getIdent (documentCreator doc)
                           case maybeIdent of
                              Just ident -> do
                                 adir <- assignmentDir ident
                                 let path = adir </> unpack filename
                                 exists <- liftIO $ doesFileExist path
                                 if exists then return (asgn, path)
                                           else setMessage ("file not found at " ++ toHtml path) >> notFound
                              Nothing ->
                                 setMessage ("failed to get document creator for " ++ toHtml filename) >> notFound
                      _ -> error "more than one assignment for this course is associated with this filename"
        where creatorAccess cid course (Entity _ doc) = do 
                    mud <- runDB $ getBy $ UniqueUserData (documentCreator doc)
                    case mud >>= userDataInstructorId . entityVal of 
                        Nothing -> return False
                        Just iid | iid == courseInstructor course -> return True
                                 | otherwise -> do mco <- runDB $ getBy (UniqueCoInstructor iid cid)
                                                   return $ not (null mco)




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
