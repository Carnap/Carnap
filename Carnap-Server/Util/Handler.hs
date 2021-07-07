module Util.Handler where

import Import
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import Yesod.Markdown
import Text.Pandoc (Meta, PandocError, MetaValue(..),Inline(..), WriterOptions(..), WrapOption(..), readerExtensions,   Pandoc(..), getTemplate, compileTemplate, lookupMeta, runIO)
import Text.Pandoc.Walk (Walkable, walk)
import Text.Hamlet (hamletFile)
import TH.RelativePaths (pathRelativeToCabalPackage)
import System.Directory (removeFile, doesFileExist, createDirectoryIfMissing)
import Util.Data
import Util.Database
import System.FilePath
import Text.Blaze.XHtml5 (ToMarkup, Markup)

minimalLayout :: ToMarkup a => a -> WidgetFor site ()
minimalLayout c = [whamlet|
                  <div.container>
                      <article>
                          #{c}
                  |]

cleanLayout :: ToWidget App a => a -> HandlerFor App Markup
cleanLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        mud <- maybeUserData
        mcourse <- maybeUserCourse
        mdoc <- maybeUserTextbookDoc
        let isInstructor = not $ null (mud >>= userDataInstructorId . entityVal)
        pc <- widgetToPageContent $(widgetFile "default-layout")
        withUrlRenderer $(hamletFile =<< pathRelativeToCabalPackage "templates/default-layout-wrapper.hamlet")

retrievePandocVal :: MonadHandler m => Maybe MetaValue -> m (Maybe [Text])
retrievePandocVal metaval = case metaval of
                        Just (MetaInlines ils) -> return $ Just (catMaybes (map fromStr ils))
                        Just (MetaList list) -> do mvals <- mapM retrievePandocVal (map Just list)
                                                   return . Just . concat . catMaybes $ mvals
                        Nothing -> return Nothing
                        x -> setMessage (toHtml ("bad yaml metadata: " ++ show x)) >> return Nothing
    where fromStr (Str x) = Just x
          fromStr _ = Nothing

retrievePandocValPure :: Monad m => Maybe MetaValue -> m (Maybe [Text])
retrievePandocValPure metaval = case metaval of
                        Just (MetaInlines ils) -> return $ Just (catMaybes (map fromStr ils))
                        Just (MetaList list) -> do mvals <- mapM retrievePandocValPure (map Just list)
                                                   return . Just . concat . catMaybes $ mvals
                        Nothing -> return Nothing
                        _ -> return Nothing
    where fromStr (Str x) = Just x
          fromStr _ = Nothing

fileToHtml :: Walkable a Pandoc => (a -> a) -> FilePath -> IO (Either String (Either PandocError Html, Meta))
fileToHtml filters path = do Markdown md <- markdownFromFile path
                             let md' = Markdown (filter ((/=) '\r') md) --remove carrage returns from dos files
                             case parseMarkdown yesodDefaultReaderOptions { readerExtensions = carnapPandocExtensions } md' of
                                 Right pd -> do let pd'@(Pandoc meta _)= walk filters pd
                                                templateOrErr <- templateFrom meta
                                                case templateOrErr of
                                                    Right template -> return $ Right $ (write template pd', meta)
                                                    Left err -> return $ Left err
                                 Left err -> return $ Left (show err)
    where write template = writePandocTrusted yesodDefaultWriterOptions { writerExtensions = carnapPandocExtensions
                                                                        , writerWrapText = WrapPreserve
                                                                        , writerTemplate = template
                                                                        , writerTableOfContents = template /= Nothing
                                                                        }
          templateFrom meta = do mtemplate <- retrievePandocValPure (lookupMeta "template" meta)
                                 case mtemplate of
                                     Just [templatename] | takeExtension (unpack templatename) == ".template" -> do
                                           let templatepath = takeDirectory path </> unpack templatename
                                           templateOrErr <- runIO $ getTemplate templatepath
                                           case templateOrErr of
                                               Left err -> return $ Left (show err)
                                               Right template -> do
                                                   compiled <- compileTemplate templatepath template
                                                   return $ case compiled of
                                                       Left err -> Left $ "template error: " ++ err
                                                       Right t -> Right $ Just t
                                     Just _ -> do return (Left "template error: Only one template file is allowd, and it must have the extension .template")
                                     _ -> return (Right Nothing)

saveTo
    :: FilePath
    -> FilePath
    -> FileInfo
    -> HandlerFor App ()
saveTo thedir fn file = do
        datadir <- appDataRoot <$> (appSettings <$> getYesod)
        let path = datadir </> thedir
        liftIO $
            do createDirectoryIfMissing True path
               e <- doesFileExist (path </> fn)
               if e then removeFile (path </> fn) else return ()
               fileMove file (path </> fn)

safeSaveTo
    :: FilePath
    -> FilePath
    -> FileInfo
    -> HandlerFor App ()
safeSaveTo thedir fn file = do
        datadir <- appDataRoot <$> (appSettings <$> getYesod)
        let path = datadir </> thedir
        e <- liftIO $ doesFileExist (path </> fn)
        if e then setMessage "Refusing to overwrite existing file"
             else liftIO $ do createDirectoryIfMissing True path
                              fileMove file (path </> fn)

isInvalidFilename :: Text -> Bool
isInvalidFilename s = not (takeFileName (unpack s) == (unpack s))

requireReferral :: Route App -> Handler ()
requireReferral route = do referer <- lookupHeader "Referer" --This is actually how it is spelled in the relevant standard
                                        >>= maybe (sendStatusJSON badRequest400 ("Bad Referer" :: Text)) pure
                           render <- getUrlRender
                           if render route == decodeUtf8 referer
                               then return ()
                               else sendStatusJSON badRequest400 ("Bad Referer" :: Text)

serveDoc :: (Document -> FilePath -> Handler a) -> Document -> FilePath -> UserId -> Handler a
serveDoc sendIt doc path creatoruid = case documentScope doc of
                                Private -> do
                                  muid <- maybeAuthId
                                  case muid of Just uid' | uid' == creatoruid -> sendIt doc path
                                               _ -> notFound
                                _ -> sendIt doc path

asFile :: Document -> FilePath -> Handler a
asFile doc path = do addHeader "Content-Disposition" $ concat
                        [ "attachment;"
                        , "filename=\"", documentFilename doc, "\""
                        ]
                     sendFile typeOctet path

asCss :: Document -> FilePath -> Handler a
asCss _ path = sendFile typeCss path

asJs :: Document -> FilePath -> Handler a
asJs _ path = sendFile typeJavascript path

--XXX YAML has no IANA mimetype, so this seems appropriate
--https://stackoverflow.com/questions/332129/yaml-media-type
asYaml :: Document -> FilePath -> Handler a
asYaml _ path = sendFile "text/x-yaml; charset=utf-8" path

---------------------
--  API UTILITIES  --
---------------------

assignmentPartOf :: (YesodPersist site, YesodPersistBackend site ~ SqlBackend) => AssignmentMetadataId -> CourseId -> YesodDB site AssignmentMetadata
assignmentPartOf asid cid = do
        as <- get asid >>= maybe (sendStatusJSON notFound404 ("No such assignment" :: Text)) pure
        if assignmentMetadataCourse as == cid then return () else sendStatusJSON notFound404 ("No such assignment" :: Text)
        return as

userFromIdent :: Text -> Handler (Entity User)
userFromIdent ident = maybeUserByIdent ident >>= maybe (sendStatusJSON notFound404 ("No such instructor" :: Text)) pure

userDataFromIdent :: Text -> Handler (Entity UserData)
userDataFromIdent ident = maybeUserDataByIdent ident >>= maybe (sendStatusJSON notFound404 ("No such instructor" :: Text)) pure

courseFromTitle :: Text -> Handler (Entity Course)
courseFromTitle coursetitle = runDB (getBy $ UniqueCourse coursetitle) >>= maybe (sendStatusJSON notFound404 ("No such course" :: Text)) pure

roleInClass :: Text -> Text -> Handler (Entity Course, Maybe (Entity CoInstructor))
roleInClass ident coursetitle = do
    courseEnt@(Entity cid course) <- courseFromTitle coursetitle
    Entity uid _ <- userFromIdent ident
    Entity _udid ud <- runDB (getBy $ UniqueUserData uid) >>= maybe (sendStatusJSON notFound404 ("No userdata for this ident" :: Text)) pure
    case userDataInstructorId ud of
        Nothing -> sendStatusJSON forbidden403 ("Not an instructor" :: Text)
        Just iid | courseInstructor course == iid -> return (courseEnt, Nothing)
        Just iid -> do coInstruct <- runDB (getBy $ UniqueCoInstructor iid cid) >>= maybe (sendStatusJSON forbidden403 ("Not an instructor for this course" :: Text)) pure
                       return (courseEnt, Just coInstruct)

canAccessClass :: Text -> Text -> Handler (Entity Course)
canAccessClass ident coursetitle = fst <$> roleInClass ident coursetitle
