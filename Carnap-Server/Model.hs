{-# LANGUAGE FlexibleInstances #-}

module Model where

import ClassyPrelude.Yesod
import Database.Persist.Quasi
import Util.Data

-- You can define all of your database entities in the entities file.
-- You can find more information on persistent and how to declare entities
-- at:
-- http://www.yesodweb.com/book/persistent/

share [mkPersist sqlSettings, mkDeleteCascade sqlSettings, mkMigrate "migrateAll"]
    $(persistFileWith lowerCaseSettings "config/models")

instructorList = do entityList <- runDB $ selectList [UserDataInstructorId !=. Nothing] []
                    return (map entityVal entityList)

instructorIdentList = do instructorEntityList <- runDB $ selectList [UserDataInstructorId !=. Nothing] []
                         userEntityList <- runDB $ selectList [UserId <-. map (userDataUserId . entityVal) instructorEntityList ] []
                         return $ map (userIdent . entityVal) userEntityList
