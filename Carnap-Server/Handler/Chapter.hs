module Handler.Chapter where

import Import
import Yesod.Markdown
import Filter.Sidenotes
import Filter.SynCheckers
import Text.Pandoc.Walk (walkM, walk)
import System.Directory (getDirectoryContents, doesDirectoryExist)
import Text.Julius (juliusFile)
import Text.Hamlet (hamletFile)
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import Control.Monad.State (evalState)

getChapterR :: Int -> Handler Html
getChapterR n = do content <- liftIO $ chapter n 
                   case content of
                       Right html -> chapterLayout $ layout html
                       Left err -> defaultLayout $ layout (show err)
    where layout c = [whamlet|
                        <div.container>
                            <article>
                                #{c}
                       |]

chapter n = do localbook <- doesDirectoryExist "book"
               let path = (if localbook then "book/chapter" else "/root/book/chapter") 
                                    ++  show n ++ ".pandoc"
               fileToHtml path

fileToHtml path = do md <- markdownFromFile path
                     let pdOrEr = parseMarkdown yesodDefaultReaderOptions md
                     let walkedOrEr  = fmap runFilters pdOrEr
                     let htmlOrEr = fmap (writePandoc yesodDefaultWriterOptions) walkedOrEr
                     return htmlOrEr

runFilters x = walk makeSynCheckers $ evalState (walkM makeSideNotes x) 0

chapterLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        pc     <- widgetToPageContent $ do
            toWidgetHead $(juliusFile "templates/command.julius")
            addScript $ StaticR ghcjs_rts_js
            addScript $ StaticR ghcjs_syncheck_lib_js
            addScript $ StaticR ghcjs_syncheck_out_js
            addStylesheet $ StaticR css_tree_css
            addStylesheet $ StaticR css_tufte_css
            $(widgetFile "default-layout")
            addScript $ StaticR ghcjs_syncheck_runmain_js
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")
