module Handler.API.Instructor where

import Import
import Util.Data (SharingScope (..))
import Data.Aeson
import Data.HashMap.Strict as HM

getAPIInstructorDocumentsR :: Text -> Handler Value
getAPIInstructorDocumentsR ident = do Entity uid _ <- runDB (getBy $ UniqueUser ident) 
                                                      >>= maybe (sendStatusJSON notFound404 ("No such instructor" :: Text)) pure
                                      docs <- runDB $ selectList [DocumentCreator ==. uid] []
                                      returnJson docs

postAPIInstructorDocumentsR :: Text -> Handler Value
postAPIInstructorDocumentsR ident = do Entity uid _ <- runDB (getBy $ UniqueUser ident)
                                                       >>= maybe (sendStatusJSON notFound404 ("No such instructor" :: Text)) pure
                                       val <- requireJsonBody :: Handler Value
                                       time <- liftIO $ getCurrentTime
                                       val' <- case val of
                                                   Object hm -> 
                                                        let hm' = HM.insert "creator" (toJSON uid) 
                                                                . HM.insert "date" (toJSON time) 
                                                                --default to private if scope is omitted
                                                                . HM.insertWith (\_ y -> y) "scope" (toJSON Private) 
                                                                $ hm 
                                                        in return $ Object hm'
                                                   _ -> sendStatusJSON badRequest400 ("improper JSON" :: Text)
                                       case fromJSON val' :: Result Document of
                                           Error e -> (sendStatusJSON badRequest400 e)
                                           Success doc -> do
                                               datadir <- appDataRoot <$> (appSettings <$> getYesod)
                                               inserted <- runDB (insertUnique doc) >>= 
                                                           maybe (sendStatusJSON conflict409 ("A document with that name already exists" :: Text)) return
                                               writeFile (datadir </> "documents" </> unpack ident </> unpack (documentFilename doc)) " " --XXX clobbers existing file
                                               returnJson inserted --should also set location header
