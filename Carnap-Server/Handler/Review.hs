module Handler.Review (getReviewR) where

import Import
import Util.Database

getReviewR :: Text -> Handler Html
getReviewR filename = 
        do (Entity key val, path) <- getAssignmentByFilename filename
           runDB $ selectList [ProblemSubmissionAssignmentId ==. Just key] []
           defaultLayout [whamlet| placeholder |]
