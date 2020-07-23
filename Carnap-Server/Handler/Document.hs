module Handler.Document where

import Import
import System.Directory (doesFileExist,getDirectoryContents)
import Yesod.Markdown
import Data.List (nub)
import Text.Pandoc (writerExtensions,writerWrapText, WrapOption(..), readerExtensions, Pandoc(..), lookupMeta)
import Text.Pandoc.Walk (walkM, walk)
import Text.Julius (juliusFile,rawJS)
import System.FilePath
import Util.Data
import Util.Database
import Util.Handler
import Filter.SynCheckers
import Filter.ProofCheckers
import Filter.Translate
import Filter.TruthTables
import Filter.CounterModelers
import Filter.Qualitative
import Filter.Sequent
import Filter.TreeDeduction
import Filter.RenderFormulas

getDocumentsR :: Handler Html
getDocumentsR =  runDB (selectList [] []) >>= documentsList "Index of All Documents"

getDocumentsByTagR :: Text -> Handler Html
getDocumentsByTagR tag = do documents <- runDB $ do tags <- selectList [TagName ==. tag] []
                                                    docs <- mapM (get . tagBearer . entityVal) tags
                                                    return $ zipWith (\(Just d) t -> Entity (tagBearer $ entityVal t) d) docs tags
                            documentsList (toHtml $ "Documents tagged " <> tag) documents

documentsList :: Html -> [Entity Document] -> Handler Html
documentsList title documents = do
                   tagMap <- forM documents $ \doc -> do
                                            tags <- runDB $ selectList [TagBearer ==. entityKey doc] []
                                            return (entityKey doc, map (tagName . entityVal) tags)
                   let tagsOf d = lookup d tagMap
                       publicDocuments = filter ((==) Public . documentScope . entityVal) documents
                       allTags = nub . concat . map snd $ tagMap
                   pubidents <- mapM (getIdent . documentCreator . entityVal) publicDocuments
                   pubmd <- mapM (getUserMD . documentCreator . entityVal) publicDocuments
                   muid <- maybeAuthId
                   case muid of
                       Just uid -> do 
                            maybeData <- runDB $ getBy $ UniqueUserData uid
                            case userDataInstructorId <$> entityVal <$> maybeData of 
                               Just id -> do
                                    let docs = filter ((==) InstructorsOnly . documentScope . entityVal) documents
                                        privateDocuments = if docs == [] then Nothing else Just docs 
                                    privmd <- mapM (getUserMD . documentCreator . entityVal) docs
                                    prividents <- mapM (getIdent . documentCreator . entityVal) docs
                                    defaultLayout $ do
                                        setTitle title
                                        $(widgetFile "documentIndex")
                               Nothing -> do let privateDocuments = Nothing
                                                 (privmd, prividents) = ([],[])
                                             defaultLayout $ do
                                                 setTitle $ title
                                                 $(widgetFile "documentIndex")
                       Nothing -> do let privateDocuments = Nothing
                                         (privmd, prividents) = ([],[])
                                     defaultLayout $ do
                                        setTitle $ title
                                        $(widgetFile "documentIndex")
    where documentCards docs idents mds tagsOf = [whamlet|
    $forall (Entity k doc,mident, mmd) <- zip3 docs idents mds
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
                            <dd.col-sm-9> #{formatTime defaultTimeLocale "%F %R UTC" $ documentDate doc}
                            $maybe tags <- tagsOf k
                                <dt.col-sm-3> Tags
                                <dd.col-sm-9>
                                        $forall tag <- tags
                                            <a.badge.badge-primary href="@{DocumentsByTagR tag}">#{tag}
                        <button.btn.btn-sm.btn-secondary type="button" onclick="window.open('@{DocumentDownloadR ident (documentFilename doc)}')">
                            <i.fa.fa-cloud-download>
    |]

-- XXX DRY up the boilplate that is shared by getDocumentDownload
getDocumentR :: Text -> Text -> Handler Html
getDocumentR ident title = do (Entity key doc, path, creatorid) <- retrieveDoc ident title
                              case documentScope doc of 
                                 Private -> do
                                   muid <- maybeAuthId
                                   case muid of
                                       Just uid' | creatorid /= uid' -> setMessage "shared file for this document not found" >> notFound
                                       Just uid' | takeExtension path == ".css" -> serveDoc asCss doc path creatorid >> notFound 
                                       Just uid' | takeExtension path == ".js" -> serveDoc asCss doc path creatorid >> notFound 
                                            --serveDoc bypasses the
                                            --remaining handlers, so the
                                            --not-found here is
                                            --a placeholder that is never
                                            --reached
                                       Just uid' -> returnFile path
                                       _ -> setMessage "shared file for this document not found" >> notFound
                                 _ | takeExtension path == ".css" -> serveDoc asCss doc path creatorid >> notFound
                                 _ | takeExtension path == ".js" -> serveDoc asJs doc path creatorid >> notFound
                                   | otherwise -> returnFile path

    where returnFile path = do
              ehtml <- liftIO $ fileToHtml path
              case ehtml of
                  Left err -> defaultLayout $ minimalLayout (show err)
                  Right (Left err,_) -> defaultLayout $ minimalLayout (show err)
                  Right (Right html, meta) -> do
                      mcss <- retrievePandocVal (lookupMeta "css" meta)
                      mjs <- retrievePandocVal (lookupMeta "js" meta)
                      defaultLayout $ do
                          toWidgetHead $(juliusFile "templates/command.julius")
                          addScript $ StaticR js_proof_js
                          addScript $ StaticR js_popper_min_js
                          addScript $ StaticR ghcjs_rts_js
                          addScript $ StaticR ghcjs_allactions_lib_js
                          addScript $ StaticR ghcjs_allactions_out_js
                          maybe (pure [()]) (mapM (addScriptRemote . pack))  mjs
                          addStylesheet $ StaticR css_tree_css
                          addStylesheet $ StaticR css_proof_css
                          addStylesheet $ StaticR css_exercises_css
                          case mcss of 
                              Nothing -> mapM addStylesheet [StaticR css_bootstrapextra_css]
                              Just ss -> mapM (addStylesheetRemote . pack) ss
                          $(widgetFile "document")
                          addScript $ StaticR ghcjs_allactions_runmain_js

getDocumentDownloadR :: Text -> Text -> Handler TypedContent
getDocumentDownloadR ident title = do (Entity key doc, path, creatoruid) <- retrieveDoc ident title
                                      serveDoc asFile doc path creatoruid

retrieveDoc :: Text -> Text -> Handler (Entity Document, FilePath, UserId)
retrieveDoc ident title = do userdir <- getUserDir ident 
                             let path = userdir </> unpack title
                             exists <- liftIO $ doesFileExist path
                             mcreator <- runDB $ getBy $ UniqueUser ident
                             case mcreator of
                                 _ | not exists -> setMessage "shared file for this document not found" >> notFound
                                 Nothing -> setMessage "document creator not found" >> notFound
                                 Just (Entity creatoruid _) -> do
                                     mdoc <- runDB $ getBy (UniqueDocument title creatoruid)
                                     case mdoc of
                                         Nothing -> setMessage "metadata for this document not found" >> notFound
                                         Just doc -> return (doc, path, creatoruid)

fileToHtml path = do Markdown md <- markdownFromFile path
                     let md' = Markdown (filter ((/=) '\r') md) --remove carrage returns from dos files
                     case parseMarkdown yesodDefaultReaderOptions { readerExtensions = carnapPandocExtensions } md' of
                         Right pd -> do let pd'@(Pandoc meta _)= walk allFilters pd
                                        return $ Right $ (write pd', meta)
                         Left e -> return $ Left e
    where write = writePandocTrusted yesodDefaultWriterOptions { writerExtensions = carnapPandocExtensions, writerWrapText = WrapPreserve }

getUserDir ident = do master <- getYesod
                      return $ (appDataRoot $ appSettings master) </> "documents" </> unpack ident

allFilters = makeTreeDeduction 
             . makeSequent 
             . makeSynCheckers 
             . makeProofChecker 
             . makeTranslate 
             . makeTruthTables 
             . makeCounterModelers 
             . makeQualitativeProblems 
             . renderFormulas
