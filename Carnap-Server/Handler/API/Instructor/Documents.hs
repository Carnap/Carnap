module Handler.API.Instructor.Documents where

import           Data.Aeson
import           Handler.API.Instructor.Types (DocumentPatch (..),
                                               DocumentPost (..))
import           Import
import           System.Directory
import           System.FilePath
import           Util.Data                    (SharingScope (..))
import           Util.Database                (documentsWithTags)
import           Util.Handler

getAPIInstructorDocumentsR :: Text -> Handler Value
getAPIInstructorDocumentsR ident = do
    Entity uid _ <- userFromIdent ident
    returnJson =<< runDB (documentsWithTags uid)

postAPIInstructorDocumentsR :: Text -> Handler Value
postAPIInstructorDocumentsR ident = do
    Entity uid _ <- userFromIdent ident
    DocumentPost {docPostScope, docPostFilename, docPostDescription, docPostTags}
        <- requireCheckJsonBody :: Handler DocumentPost
    time <- liftIO getCurrentTime

    when (badFileName docPostFilename)
        $ sendStatusJSON badRequest400 ("Improper filename" :: Text)
    let doc = Document
            { documentFilename = docPostFilename
            , documentCreator = uid
            , documentDate = time
            , documentScope = fromMaybe Private docPostScope
            , documentDescription = docPostDescription
            }

    dir <- docDir ident
    liftIO $ createDirectoryIfMissing True dir
    path <- docFilePath ident doc
    liftIO (doesFileExist path) >>= --don't clobber and annex
        flip when (sendStatusJSON conflict409 ("A document with that name already exists." :: Text))
    inserted <- runDB $ do
        docId <- insertUnique doc >>=
            maybe (sendStatusJSON conflict409 ("A document with that name already exists." :: Text)) return
        insertMany_ (Tag docId <$> concat docPostTags)
        return docId
    writeFile path " "
    render <- getUrlRender
    addHeader "Location" (render $ APIInstructorDocumentR ident inserted)
    sendStatusJSON created201 inserted

    where badFileName s = takeFileName (unpack s) /= unpack s

getAPIInstructorDocumentR :: Text -> DocumentId -> Handler Value
getAPIInstructorDocumentR ident docid = do Entity uid _ <- userFromIdent ident
                                           doc <- runDB (get docid) >>= maybe (sendStatusJSON notFound404 ("No such document" :: Text)) pure
                                           checkUID doc uid
                                           returnJson doc

patchAPIInstructorDocumentR :: Text -> DocumentId -> Handler Value
patchAPIInstructorDocumentR ident docid = do
    Entity uid _ <- userFromIdent ident
    doc <- runDB (get docid) >>= maybe (sendStatusJSON notFound404 ("No such document" :: Text)) pure
    checkUID doc uid

    DocumentPatch {patchScope, patchDescription, patchTags}
        <- requireCheckJsonBody :: Handler DocumentPatch
    doc' <- runDB $ do
        putMany (Tag docid <$> concat patchTags)
        updateGet docid
              $ maybeUpdate DocumentScope patchScope
             ++ maybeUpdate DocumentDescription patchDescription

    returnJson doc'

    where maybeUpdate field (Just val) = [field =. val]
          maybeUpdate _     Nothing    = []

getAPIInstructorDocumentDataR :: Text -> DocumentId -> Handler Value
getAPIInstructorDocumentDataR ident docid = do Entity uid _ <- userFromIdent ident
                                               doc <- runDB (get docid) >>= maybe (sendStatusJSON notFound404 ("No such document" :: Text)) pure
                                               checkUID doc uid
                                               docFilePath ident doc >>= asFile doc

putAPIInstructorDocumentDataR :: Text -> DocumentId -> Handler Value
putAPIInstructorDocumentDataR ident docid = do Entity uid _ <- userFromIdent ident
                                               doc <- runDB (get docid) >>= maybe (sendStatusJSON notFound404 ("No such document" :: Text)) pure
                                               checkUID doc uid
                                               path <- docFilePath ident doc
                                               connect rawRequestBody (sinkFile path)
                                               returnJson ("contents updated" :: Text)

docDir :: Text -> Handler FilePath
docDir ident = do datadir <- appDataRoot <$> (appSettings <$> getYesod)
                  return (datadir </> "documents" </> unpack ident)

docFilePath :: Text -> Document -> Handler FilePath
docFilePath ident doc = do docdir <- docDir ident
                           return (docdir </> unpack (documentFilename doc))

checkUID :: MonadHandler m => Document -> Key User -> m ()
checkUID doc uid | documentCreator doc == uid = return ()
                 | otherwise = sendStatusJSON forbidden403 ("Document not owned by this instructor" :: Text)
