{-# LANGUAGE ConstraintKinds #-}

module Import.NoFoundation
    ( module Import
    , PersistentSite
    ) where

import ClassyPrelude.Yesod   as Import
import Model                 as Import
import Settings              as Import
import Settings.StaticFiles  as Import
import Yesod.Auth            as Import
import Yesod.Core.Types      as Import (loggerSet)
import Yesod.Default.Config2 as Import

-- | A type alias to shorten the mess required to have generic functions using
--   the database (used for modules when we cannot name the @App@ instance
--   since they are imported by Foundation where it is defined)
type PersistentSite site =
    (PersistUniqueRead (YesodPersistBackend site),
     PersistUniqueWrite (YesodPersistBackend site),
     PersistQueryRead (YesodPersistBackend site),
     PersistQueryWrite (YesodPersistBackend site),
     YesodPersist site,
     YesodAuthPersist site,
     AuthId site ~ Key User,
     AuthEntity site ~ User,
     BaseBackend (YesodPersistBackend site) ~ SqlBackend)

