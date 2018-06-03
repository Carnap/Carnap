module Handler.Document where

import Import
import System.Directory (doesFileExist,getDirectoryContents)
import Yesod.Markdown
import Text.Pandoc.Walk (walkM, walk)
import Text.Julius (juliusFile,rawJS)
import Util.Data
import Util.Database
import Filter.SynCheckers
import Filter.ProofCheckers
import Filter.Translate
import Filter.TruthTables

getDocumentsR :: Handler Html
getDocumentsR = do publicDocuments <- runDB $ selectList [DocumentScope ==. Public] []
                   pubidents <- mapM (getIdent . documentCreator . entityVal) publicDocuments
                   pubmd <- mapM (getUserMD . documentCreator . entityVal) publicDocuments
                   muid <- maybeAuthId
                   case muid of
                       Just uid -> do 
                            maybeData <- runDB $ getBy $ UniqueUserData uid
                            case userDataInstructorId <$> entityVal <$> maybeData of 
                               Just id -> do
                                    docs <- runDB $ selectList [DocumentScope ==. InstructorsOnly] []
                                    let privateDocuments = Just docs 
                                    privmd <- mapM (getUserMD . documentCreator . entityVal) docs
                                    prividents <- mapM (getIdent . documentCreator . entityVal) docs
                                    defaultLayout $ do
                                        setTitle $ "Index of Documents"
                                        $(widgetFile "documentIndex")
                               Nothing -> do let privateDocuments = Nothing
                                                 (privmd, prividents) = ([],[])
                                             defaultLayout $ do
                                                 setTitle $ "Index of Documents"
                                                 $(widgetFile "documentIndex")
                       Nothing -> do let privateDocuments = Nothing
                                         (privmd, prividents) = ([],[])
                                     defaultLayout $ do
                                        setTitle $ "Index of Documents"
                                        $(widgetFile "documentIndex")
    where documentCards docs idents mds = [whamlet|
    $forall (doc,mident, mmd) <- zip3 (map entityVal docs) idents mds
        $maybe ident <- mident
            $maybe md <- mmd
                <div.card>
                    <div.card-header>
                        <a href=@{DocumentR ident (documentFilename doc)}>
                            #{documentFilename doc}
                    <div.card-block>
                        <dl.row>
                            <dt.col-sm-3> Title
                            <dd.col-sm-9> #{documentFilename doc}
                            $maybe desc <- documentDescription doc
                                <dt.col-sm-3> Description
                                <dd.col-sm-9> #{desc}
                            <dt.col-sm-3> Creator
                            <dd.col-sm-9> #{userDataFirstName md} #{userDataLastName md}
                            <dt.col-sm-3> Created on
                            <dd.col-sm-9> #{show $ documentDate doc}
                        <button.btn.btn-sm.btn-secondary type="button" onclick="window.open('@{DocumentDownloadR ident (documentFilename doc)}')">
                            <i.fa.fa-cloud-download>

    |]

-- XXX DRY up the boilplate that is shared by getDocumentDownload
getDocumentR :: Text -> Text -> Handler Html
getDocumentR ident title = do userdir <- getUserDir ident 
                              let path = userdir </> unpack title
                              exists <- lift $ doesFileExist path
                              mcreator <- runDB $ getBy $ UniqueUser ident
                              case mcreator of
                                  _ | not exists -> defaultLayout $ layout ("shared file for this document not found" :: Text)
                                  Nothing -> defaultLayout $ layout ("document creator not found" :: Text)
                                  Just (Entity uid _) -> do
                                      mdoc <- runDB $ getBy (UniqueDocument title uid)
                                      case mdoc of
                                          Nothing -> defaultLayout $ layout ("metadata for this document not found" :: Text)
                                          Just (Entity key doc) -> do
                                              case documentScope doc of 
                                                Private -> defaultLayout $ layout ("shared file for this document not found" :: Text)
                                                _ -> do
                                                  ehtml <- lift $ fileToHtml path
                                                  case ehtml of
                                                      Left err -> defaultLayout $ layout (show err)
                                                      Right html -> do
                                                          defaultLayout $ do
                                                              toWidgetHead $(juliusFile "templates/command.julius")
                                                              addScript $ StaticR js_popper_min_js
                                                              addScript $ StaticR ghcjs_rts_js
                                                              addScript $ StaticR ghcjs_allactions_lib_js
                                                              addScript $ StaticR ghcjs_allactions_out_js
                                                              addStylesheet $ StaticR css_exercises_css
                                                              addStylesheet $ StaticR css_tree_css
                                                              addStylesheet $ StaticR css_exercises_css
                                                              $(widgetFile "document")
                                                              addScript $ StaticR ghcjs_allactions_runmain_js

    where layout c = [whamlet|
                        <div.container>
                            <article>
                                #{c}
                        |]

getDocumentDownloadR :: Text -> Text -> Handler TypedContent
getDocumentDownloadR ident title = do userdir <- getUserDir ident 
                                      let path = userdir </> unpack title
                                      exists <- lift $ doesFileExist path
                                      mcreator <- runDB $ getBy $ UniqueUser ident
                                      case mcreator of
                                          _ | not exists -> notFound
                                          Nothing -> notFound
                                          Just (Entity uid _) -> do
                                              mdoc <- runDB $ getBy (UniqueDocument title uid)
                                              case mdoc of
                                                  Nothing -> notFound
                                                  Just (Entity key doc) -> do
                                                      case documentScope doc of 
                                                        Private -> notFound
                                                        _ -> do
                                                          addHeader "Content-Disposition" $ concat
                                                            [ "attachment;"
                                                            , "filename=\""
                                                            , documentFilename doc
                                                            , "\""
                                                            ]
                                                          sendFile typeOctet path

fileToHtml path = do Markdown md <- markdownFromFile path
                     let md' = Markdown (filter ((/=) '\r') md) --remove carrage returns from dos files
                     case parseMarkdown yesodDefaultReaderOptions md' of
                         Right pd -> do let pd' = walk allFilters pd
                                        return $ Right $ writePandocTrusted yesodDefaultWriterOptions pd'
                         Left e -> return $ Left e
    where allFilters = (makeSynCheckers . makeProofChecker . makeTranslate . makeTruthTables)

getUserDir ident = do master <- getYesod
                      return $ (appDataRoot $ appSettings master) </> "shared" </> unpack ident
