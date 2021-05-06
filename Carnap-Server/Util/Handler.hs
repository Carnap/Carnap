module Util.Handler where

import Import
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import Yesod.Markdown
import Text.Pandoc (MetaValue(..),Inline(..), writerExtensions,writerWrapText, WrapOption(..), readerExtensions, Pandoc(..))
import Text.Pandoc.Walk (walkM, walk)
import Text.Julius (juliusFile,rawJS)
import Text.Hamlet (hamletFile)
import TH.RelativePaths (pathRelativeToCabalPackage)
import System.Directory (removeFile, doesFileExist, createDirectoryIfMissing)
import Util.Data
import Util.Database
import System.FilePath

minimalLayout c = [whamlet|
                  <div.container>
                      <article>
                          #{c}
                  |]

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

retrievePandocVal metaval = case metaval of 
                        Just (MetaInlines ils) -> return $ Just (catMaybes (map fromStr ils))
                        Just (MetaList list) -> do mcsses <- mapM retrievePandocVal (map Just list) 
                                                   return . Just . concat . catMaybes $ mcsses
                        Nothing -> return Nothing
                        x -> setMessage (toHtml ("bad yaml metadata: " ++ show x)) >> return Nothing
    where fromStr (Str x) = Just x
          fromStr _ = Nothing

fileToHtml filters path = do Markdown md <- markdownFromFile path
                             let md' = Markdown (filter ((/=) '\r') md) --remove carrage returns from dos files
                             case parseMarkdown yesodDefaultReaderOptions { readerExtensions = carnapPandocExtensions } md' of
                                 Right pd -> do let pd'@(Pandoc meta _)= walk filters pd
                                                return $ Right $ (write pd', meta)
                                 Left e -> return $ Left e
    where write = writePandocTrusted yesodDefaultWriterOptions { writerExtensions = carnapPandocExtensions, writerWrapText = WrapPreserve }

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
