{-# LANGUAGE TypeApplications #-}

module Util.Sql where

import Carnap.GHCJS.SharedTypes (ProblemSource (Book))
import ClassyPrelude hiding (on)
import Database.Esqueleto.Experimental
import Model

-- NOTE: probably should use a newer esqueleto with the type level strings e.g. ps ^. #assignmentId
-- but I don't have time to port the codebase re other updates

problemsCompletedByUserIn ::
    MonadIO m =>
    UserId ->
    CourseId ->
    SqlPersistT m [Entity ProblemSubmission]
problemsCompletedByUserIn uid cid = do
    select $ do
        (ps :& amd) <-
            from $
                table @ProblemSubmission
                    -- also include problem submissions not attached to an assignment ie book ones
                    `leftJoin` table @AssignmentMetadata
                    `on` (\(ps :& amd) -> ps ^. ProblemSubmissionAssignmentId ==. amd ?. AssignmentMetadataId)
        where_ $
            ps ^. ProblemSubmissionUserId ==. val uid
                &&. (amd ?. AssignmentMetadataCourse ==. val (Just cid) ||. ps ^. ProblemSubmissionSource ==. val Book)
        pure ps
