{-#LANGUAGE DeriveGeneric #-}
module Util.Database where

import Import
import Data.IntMap (IntMap)
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

class Problem p where
        problem :: p -> Text
        submitted :: p -> UTCTime
        assignment :: p -> Maybe AssignmentMetadataId

instance Problem SyntaxCheckSubmission where
        problem (SyntaxCheckSubmission prob _ _ _ _) = prob
        submitted (SyntaxCheckSubmission _ time _ _ _) = time
        assignment (SyntaxCheckSubmission _ _ _ _ key) = key

instance Problem TranslationSubmission where
        problem (TranslationSubmission prob _ _ _ _) = prob
        submitted (TranslationSubmission _ time _ _ _) = time
        assignment (TranslationSubmission _ _ _ _ key) = key

instance Problem TruthTableSubmission where
        problem (TruthTableSubmission prob _ _ _ _) = prob
        submitted (TruthTableSubmission _ time _ _ _) = time
        assignment (TruthTableSubmission _ _ _ _ key) = key

instance Problem DerivationSubmission where
        problem (DerivationSubmission prob _ _ _ _ _) = prob
        submitted (DerivationSubmission _ _ time _ _ _) = time
        assignment (DerivationSubmission _ _ _ _ _ key) = key

subsByIdAndSource Nothing _ = return ([],[],[],[])
subsByIdAndSource (Just cid) v = 
        do synsubs   <- runDB $ selectList (queryBy SyntaxCheckSubmissionUserId SyntaxCheckSubmissionSource) []
           transsubs <- runDB $ selectList (queryBy TranslationSubmissionUserId TranslationSubmissionSource) []
           dersubs   <- runDB $ selectList (queryBy DerivationSubmissionUserId DerivationSubmissionSource) []
           ttsubs    <- runDB $ selectList (queryBy TruthTableSubmissionUserId TruthTableSubmissionSource) []
           return (map entityVal synsubs, map entityVal transsubs, map entityVal dersubs, map entityVal ttsubs)
    where queryBy :: EntityField a (Key User) -> EntityField a ByteString -> [Filter a]
          queryBy id src = [ id ==. v , src ==. (toStrict . encode) (CourseAssignment cid) ] ||. [ id ==. v , src ==. (toStrict . encode) (CarnapTextbook)]

type BookProblemSets = Maybe (IntMap UTCTime)

instance ToJSON ProblemSource
instance FromJSON ProblemSource
