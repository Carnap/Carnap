module Handler.Serve where

import Import
import System.Directory (doesFileExist)
import Yesod.Markdown
import Data.List (nub)
import Text.Pandoc (writerExtensions,writerWrapText, WrapOption(..), readerExtensions, Pandoc(..), lookupMeta)
import Text.Pandoc.Walk (walkM, walk)
import Text.Julius (juliusFile,rawJS)
import TH.RelativePaths (pathRelativeToCabalPackage)
import System.FilePath as FP (takeExtension,joinPath)
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

-- XXX DRY up the boilplate that is shared by getDocumentDownload
getServeR :: Text -> [Text] -> Handler Html
getServeR base components = do app <- getYesod
                               let root = appDataRoot $ appSettings app
                                   path = case components of 
                                            [] -> FP.joinPath (unpack root:unpack base:["index.md"])
                                            _ -> FP.joinPath (unpack root:unpack base:map unpack components)
                               liftIO (doesFileExist path) >>= \exists -> if exists then return () else notFound
                               case () of
                                   () | takeExtension path == ".css" -> sendFile typeCss path >> notFound
                                      | takeExtension path == ".js" -> sendFile typeJavascript path >> notFound
                                      | takeExtension path == ".png" -> sendFile typePng path >> notFound
                                      | takeExtension path == ".html" -> sendFile typeHtml path >> notFound
                                      | takeExtension path == ".jpg" -> sendFile typeJpeg path >> notFound
                                      | takeExtension path == ".jpeg" -> sendFile typeJpeg path >> notFound
                                      | takeExtension path == ".gif" -> sendFile typeGif path >> notFound
                                      | takeExtension path == ".svg" -> sendFile typeGif path >> notFound
                                      | otherwise -> returnFile path
    where returnFile path = do
              ehtml <- liftIO $ fileToHtml allFilters path
              case ehtml of
                  Left err -> defaultLayout $ minimalLayout (show err)
                  Right (Left err,_) -> defaultLayout $ minimalLayout (show err)
                  Right (Right html, meta) -> do
                      mcss <- retrievePandocVal (lookupMeta "css" meta)
                      mjs <- retrievePandocVal (lookupMeta "js" meta)
                      defaultLayout $ do
                          addScript $ StaticR js_proof_js
                          addScript $ StaticR js_popper_min_js
                          addScript $ StaticR ghcjs_rts_js
                          addScript $ StaticR ghcjs_allactions_lib_js
                          addScript $ StaticR ghcjs_allactions_out_js
                          maybe (pure [()]) (mapM (addScriptRemote))  mjs
                          addStylesheet $ StaticR css_tree_css
                          addStylesheet $ StaticR css_proof_css
                          addStylesheet $ StaticR css_exercises_css
                          case mcss of
                              Nothing -> mapM addStylesheet [StaticR css_bootstrapextra_css]
                              Just ss -> mapM addStylesheetRemote ss
                          $(widgetFile "document")
                          addScript $ StaticR ghcjs_allactions_runmain_js

allFilters = makeTreeDeduction
             . makeSequent
             . makeSynCheckers
             . makeProofChecker
             . makeTranslate
             . makeTruthTables
             . makeCounterModelers
             . makeQualitativeProblems
             . renderFormulas
