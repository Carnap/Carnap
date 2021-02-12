module Handler.API.Instructor where

import Import

getAPIInstructorDocumentsR :: Text -> Handler Value
getAPIInstructorDocumentsR ident = do Entity uid usr <- runDB (getBy $ UniqueUser ident)
                                                        >>= maybe (sendStatusJSON notFound404 ("No such instructor" :: Text)) pure
                                      docs <- runDB $ selectList [DocumentCreator ==. uid] []
                                      returnJson docs
