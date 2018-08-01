{-#LANGUAGE DeriveGeneric #-}
module Util.Database where

import Import
import Data.IntMap (IntMap)
import System.Directory (doesFileExist,getDirectoryContents)
import Carnap.GHCJS.SharedTypes(ProblemSource(..))
import Data.Aeson (encode,decode, decodeStrict)

-- | Try to insert a piece of data into the database, returning False in
-- case of a clash
tryInsert s = runDB $ do munique <- checkUnique s
                         case munique of                  
                              (Just _) -> return False    
                              Nothing  -> do insert s
                                             return True

-- | retrieve a UserId = Key User, from the user's ident.
fromIdent ident = do mident <- runDB (getBy $ UniqueUser ident)
                     case mident of 
                        Nothing -> setMessage ("no user " ++ toHtml ident) >> notFound
                        Just (Entity k _) -> return k

-- | retrieve an ident from a UserId
getIdent uid = do muser <- runDB $ get uid
                  case muser of
                      Just usr -> return $ Just (userIdent usr)
                      Nothing -> return Nothing

-- | given a UserId, return the userdata or redirect to
-- registration
checkUserData uid = do maybeData <- runDB $ getBy $ UniqueUserData uid
                       muser <- runDB $ get uid
                       case muser of
                           Nothing -> do setMessage "no user found"  
                                         redirect HomeR
                           Just u -> case maybeData of
                              Nothing -> redirect (RegisterR (userIdent u))
                              Just (Entity _ userdata) -> return userdata

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
           (course,cid) <- case userDataEnrolledIn ud of
                            Just cid -> do Just course <- runDB $ get cid
                                           return (course,cid)
                            Nothing -> do setMessage "you need to be enrolled in a course to access assignments"
                                          redirect HomeR
           Entity _ instructor <- udByInstructorId $ courseInstructor course
           retrieveAssignment filename (userDataUserId instructor) cid

getAssignmentByCourse coursetitle filename = 
        do Entity uid _ <- requireAuth
           mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           case mcourse of 
             Nothing -> setMessage "no class with this title" >> notFound
             Just (Entity cid _) -> retrieveAssignment filename uid cid

getAssignmentByOwner ident filename =
        do Entity uid _ <- requireAuth
           ud <- checkUserData uid
           uid <- fromIdent ident
           case userDataEnrolledIn ud of
             Nothing -> do setMessage "you need to be enrolled in a course to access assignments" >> redirect HomeR
             Just cid -> retrieveAssignment filename uid cid

getAssignmentByCourseAndOwner coursetitle ident filename =
        do uid <- fromIdent ident
           mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           case mcourse of
             Nothing -> do setMessage "no class with this title" >> notFound
             Just (Entity cid _) -> retrieveAssignment filename uid cid

checkCourseOwnership coursetitle = do
           mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           Entity uid _ <- requireAuth
           case mcourse of 
             Nothing -> setMessage "course not found" >> notFound
             Just (Entity cid course) -> do
               Just user <- runDB (get uid)
               classes <- classesByInstructorIdent (userIdent user)
               if course `elem` map entityVal classes 
                   then return () 
                   else permissionDenied "this doesn't appear to be your course"

retrieveAssignment filename creatorUid cid = do
           mdoc <- runDB $ getBy (UniqueDocument filename creatorUid)
           case mdoc of 
                Nothing -> setMessage ("can't find document record with filename " ++ toHtml filename) >> notFound
                Just (Entity docid doc) -> do
                   Just ident <- getIdent creatorUid
                   adir <- assignmentDir ident
                   let path = adir </> unpack filename
                   exists <- lift $ doesFileExist path
                   ment <- runDB $ getBy $ UniqueAssignment docid cid
                   case ment of
                      Just ent | exists -> return (ent, path)
                               | not exists -> setMessage ("file not found at " ++ toHtml path) >> notFound
                      _ -> permissionDenied "you need to be enrolled in a course to access assignments"

-- | given a UserId, return Just the user data or Nothing
getUserMD uid = do mmd <- runDB $ getBy $ UniqueUserData uid
                   case entityVal <$> mmd of
                       Just md -> return $ Just md
                       Nothing -> return Nothing

-- | given a CourseId, return the associated book problem sets
getProblemSets cid = do mcourse <- runDB $ get cid
                        return $ mcourse >>= courseTextbookProblems

-- | classes by instructor Ident
classesByInstructorIdent ident = runDB $ do muent <- getBy $ UniqueUser ident
                                            mudent <- case entityKey <$> muent of 
                                                           Just uid -> getBy $ UniqueUserData uid
                                                           Nothing -> return Nothing
                                            case (entityVal <$> mudent) >>= userDataInstructorId of
                                                Just instructordata -> selectList [CourseInstructor ==. instructordata ] []
                                                Nothing -> return []
                                 

documentsByInstructorIdent ident = runDB $ do muent <- getBy $ UniqueUser ident
                                              case entityKey <$> muent of
                                                  Just uid -> selectList [DocumentCreator ==. uid] []
                                                  Nothing -> return []
                                   
-- | derived rules by userId
getDerivedRules uid = do savedRules <- runDB $ selectList 
                                               [SavedDerivedRuleUserId ==. uid] []
                         case savedRules of 
                             [] -> return Nothing
                             _  -> return $ Just (map entityVal savedRules)

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

problemQuery uid asl = [ ProblemSubmissionUserId ==. uid] 
                            ++ foldr (||.) [ProblemSubmissionSource ==. Book] (map assignmentQuery asl)
        where assignmentQuery as = [ProblemSubmissionSource ==. Assignment (show as) ]
