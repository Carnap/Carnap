module Handler.Chapter where

import Import
import Yesod.Markdown
import Filter.Sidenotes
import Filter.SynCheckers
import Filter.ProofCheckers
import Filter.Translate
import Filter.Diagrams
import Text.Pandoc.Walk (walkM, walk)
import System.Directory (doesDirectoryExist)
import Text.Julius (juliusFile)
import Text.Hamlet (hamletFile)
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import Control.Monad.State (evalState, evalStateT)

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
                     case parseMarkdown yesodDefaultReaderOptions md of
                         Right pd -> do pd' <- runFilters pd
                                        return $ Right $ writePandoc yesodDefaultWriterOptions pd'
                         Left e -> return $ Left e

runFilters = let walkNotes y = evalState (walkM makeSideNotes y) 0
                 walkProblems y = walk (makeSynCheckers . makeProofChecker . makeTranslate ) y
                 walkDiagrams y = evalStateT (walkM makeDiagrams y) []
                   in walkDiagrams . walkNotes . walkProblems

-- TODO: get some info about which ghcjs widgets are used, load those, then
    -- load the page, then preload the rest
chapterLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        pc     <- widgetToPageContent $ do
            toWidgetHead $(juliusFile "templates/command.julius")
            addScript $ StaticR ghcjs_rts_js
            addScript $ StaticR ghcjs_allactions_lib_js
            addScript $ StaticR ghcjs_allactions_out_js
            addStylesheet $ StaticR css_tree_css
            addStylesheet $ StaticR css_tufte_css
            addStylesheet $ StaticR css_tuftextra_css
            $(widgetFile "default-layout")
            addScript $ StaticR ghcjs_allactions_runmain_js
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")
