module Util.Database where

import Import

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

-- | given an ident and a UserId, return the userdata or redirect to
-- registration
checkUserData ident uid = do maybeData <- runDB $ getBy $ UniqueUserData uid
                             case maybeData of
                                Nothing -> redirect (RegisterR ident)
                                Just (Entity _ userdata) -> return userdata
