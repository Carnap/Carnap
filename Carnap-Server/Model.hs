{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Model where

import ClassyPrelude.Yesod
import Database.Persist.Quasi
import Util.Data
import TH.RelativePaths (pathRelativeToCabalPackage)
import Carnap.GHCJS.SharedTypes(ProblemSource(..),ProblemType(..),ProblemData(..), SomeRule(..))

-- You can define all of your database entities in the entities file.
-- You can find more information on persistent and how to declare entities
-- at:
-- http://www.yesodweb.com/book/persistent/

share [mkPersist sqlSettings, mkDeleteCascade sqlSettings, mkMigrate "migrateAll"]
    $(persistFileWith lowerCaseSettings =<< (pathRelativeToCabalPackage "config/models"))

instructorIdentList = do instructorEntityList <- runDB $ selectList [UserDataInstructorId !=. Nothing] []
                         userEntityList <- runDB $ selectList [UserId <-. map (userDataUserId . entityVal) instructorEntityList ] []
                         return $ map (userIdent . entityVal) userEntityList
