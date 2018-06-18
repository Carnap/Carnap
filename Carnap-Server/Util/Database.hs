{-#LANGUAGE DeriveGeneric #-}
module Util.Database where

import Import
import Data.IntMap (IntMap)
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
fromIdent ident = runDB $ do (Just (Entity k _)) <- getBy $ UniqueUser ident 
                             return k

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
udByInstructorId id = do [uid] <- runDB $ selectList [UserDataInstructorId ==. Just id] []
                         return uid

getProblemQuery uid cid = do asl <- runDB $ map entityKey <$> selectList [AssignmentMetadataCourse ==. cid] []
                             return $ problemQuery uid asl

problemQuery uid asl = [ ProblemSubmissionUserId ==. uid] 
                            ++ foldr (||.) [ProblemSubmissionSource ==. Book] (map assignmentQuery asl)
        where assignmentQuery as = [ProblemSubmissionSource ==. Assignment (show as) ]
