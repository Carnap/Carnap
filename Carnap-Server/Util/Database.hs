{-#LANGUAGE DeriveGeneric #-}
module Util.Database where

import Import
import Data.IntMap (IntMap)
import Data.Aeson (decode)

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

-- | given a CourseId, return the associated book problem sets
getProblemSets cid = do mcourse <- runDB $ get cid
                        return $ mcourse >>= courseTextbookProblems

-- | classes by instructor Ident
classesByInstructorIdent ident = do centlist <- runDB $ do muent <- getBy $ UniqueUser ident
                                                           mudent <- case entityKey <$> muent of 
                                                                          Just uid -> getBy $ UniqueUserData uid
                                                                          Nothing -> return Nothing
                                                           case (entityVal <$> mudent) >>= userDataInstructorId of
                                                               Just instructordata -> selectList [CourseInstructor ==. instructordata ] []
                                                               Nothing -> return []
                                    return centlist

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

data ProblemSource = CarnapTextbook
                   | CourseAssignment CourseId
      deriving (Generic,Show,Read,Eq)

type BookProblemSets = Maybe (IntMap UTCTime)

instance ToJSON ProblemSource
instance FromJSON ProblemSource
