module Handler.API.Instructor where

import Import
import Util.Data (SharingScope (..))
import Util.Handler
import Data.Aeson
import Data.HashMap.Strict as HM

getAPIInstructorDocumentsR :: Text -> Handler Value
getAPIInstructorDocumentsR ident = do Entity uid _ <- userFromIdent ident
                                      docs <- runDB $ selectList [DocumentCreator ==. uid] []
                                      returnJson docs

postAPIInstructorDocumentsR :: Text -> Handler Value
postAPIInstructorDocumentsR ident = do Entity uid _ <- userFromIdent ident
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
                                               path <- docFilePath ident doc
                                               inserted <- runDB (insertUnique doc) >>= 
                                                           maybe (sendStatusJSON conflict409 ("A document with that name already exists" :: Text)) return
                                               writeFile path " " --XXX clobbers existing file
                                               returnJson inserted --should also set location header

getAPIInstructorDocumentR :: Text -> DocumentId -> Handler Value
getAPIInstructorDocumentR ident docid = do Entity uid _ <- userFromIdent ident 
                                           doc <- runDB (get docid) >>= maybe (sendStatusJSON notFound404 ("No such document" :: Text)) pure
                                           if documentCreator doc == uid
                                               then returnJson doc
                                               else sendStatusJSON forbidden403 ("Document not owned by this instructor" :: Text)

getAPIInstructorDocumentDataR :: Text -> DocumentId -> Handler Value
getAPIInstructorDocumentDataR ident docid = do Entity uid _ <- userFromIdent ident 
                                               doc <- runDB (get docid) >>= maybe (sendStatusJSON notFound404 ("No such document" :: Text)) pure
                                               if documentCreator doc == uid
                                                   then docFilePath ident doc >>= asFile doc 
                                                   else sendStatusJSON forbidden403 ("Document not owned by this instructor" :: Text)

putAPIInstructorDocumentDataR :: Text -> DocumentId -> Handler Value
putAPIInstructorDocumentDataR ident docid = do Entity uid _ <- userFromIdent ident 
                                               doc <- runDB (get docid) >>= maybe (sendStatusJSON notFound404 ("No such document" :: Text)) pure
                                               if documentCreator doc == uid
                                                   then do path <- docFilePath ident doc 
                                                           connect rawRequestBody (sinkFile path)
                                                           sendStatusJSON created201 ("contents updated" :: Text)
                                                   else sendStatusJSON forbidden403 ("Document not owned by this instructor" :: Text)

userFromIdent :: Text -> Handler (Entity User)
userFromIdent ident = runDB (getBy $ UniqueUser ident) >>= maybe (sendStatusJSON notFound404 ("No such instructor" :: Text)) pure

docFilePath :: Text -> Document -> Handler FilePath
docFilePath ident doc = do datadir <- appDataRoot <$> (appSettings <$> getYesod)
                           return (datadir </> "documents" </> unpack ident </> unpack (documentFilename doc))
