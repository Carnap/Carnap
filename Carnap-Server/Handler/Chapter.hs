module Handler.Chapter where

import Import
import Yesod.Markdown
import Data.Char (isDigit)
import Filter.Sidenotes
import Filter.SynCheckers
import Filter.ProofCheckers
import Filter.Translate
import Filter.Diagrams
import Filter.TruthTables
import Filter.CounterModelers
import Filter.Qualitative
import Text.Pandoc
import Text.Pandoc.Walk (walkM, walk)
import System.Directory (getDirectoryContents)
import Text.Julius (juliusFile)
import Text.Hamlet (hamletFile)
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import Control.Monad.State (evalState, evalStateT)

-- XXX Fair amount of code-duplication between this and Handler/Book.hs. Perhaps merge those modules.

getChapterR :: Int -> Handler Html
getChapterR n = do bookdir <- appBookRoot <$> (appSettings <$> getYesod)
                   cdir <- liftIO $ getDirectoryContents bookdir
                   content <- liftIO $ content n cdir bookdir 
                   case content of
                       Right (Right html) -> chapterLayout  
                            [whamlet|
                                <div.container>
                                    <article>
                                        #{html}
                                        <nav.nextAndPrev>
                                            <p>
                                                $if (n > 1)
                                                    <a href="@{ChapterR (n - 1)}">
                                                        Previous Chapter
                                                $if ((n > 1) && (n < (length cdir - 3)))
                                                    <span>∙
                                                $if (n < (length cdir - 3))
                                                    <a href="@{ChapterR (n + 1)}">
                                                        Next Chapter
                            |]

                       Right (Left err) -> defaultLayout 
                                      [whamlet|
                                        <div.container>
                                            <article>
                                                #{show err}
                                       |]
                       Left err -> defaultLayout 
                                      [whamlet|
                                        <div.container>
                                            <article>
                                                #{show err}
                                       |]

content n cdir cdirp = do let matches = filter (\x -> (show n ++ ".pandoc") == dropWhile (not . isDigit) x) cdir
                          case matches of
                              [] -> do print "no matches"
                                       fileToHtml cdirp ""
                              (m:ms)  -> fileToHtml cdirp m

fileToHtml path m = do md <- markdownFromFile (path ++ m)
                       case parseMarkdown yesodDefaultReaderOptions { readerExtensions = exts } md of
                           Right pd -> do pd' <- runFilters path pd 
                                          return $ Right $ writePandocTrusted yesodDefaultWriterOptions { writerExtensions = exts } pd'
                           Left e -> return $ Left e
    where exts = extensionsFromList 
                    [ Ext_raw_html
                    , Ext_markdown_in_html_blocks
                    , Ext_auto_identifiers
                    , Ext_tex_math_dollars
                    , Ext_fenced_code_blocks
                    , Ext_backtick_code_blocks
                    , Ext_line_blocks
                    , Ext_fancy_lists
                    , Ext_definition_lists
                    , Ext_example_lists
                    , Ext_simple_tables
                    , Ext_multiline_tables
                    , Ext_footnotes
                    , Ext_fenced_code_attributes
                    ]

runFilters path = let walkNotes y = evalState (walkM makeSideNotes y) 0
                      walkProblems y = walk (makeSynCheckers . makeProofChecker . makeTranslate . makeTruthTables . makeCounterModelers . makeQualitativeProblems) y
                      walkDiagrams y = evalStateT (walkM (makeDiagrams path) y) []
                   in walkDiagrams . walkNotes . walkProblems

chapterLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        instructors <- instructorIdentList
        pc <- widgetToPageContent $ do
            toWidgetHead $(juliusFile "templates/command.julius")
            toWidgetHead $(juliusFile "templates/status-warning.julius")
            toWidgetHead [julius|var submission_source="book";|]
            addScript $ StaticR js_popper_min_js
            addScript $ StaticR ghcjs_rts_js
            addScript $ StaticR ghcjs_allactions_lib_js
            addScript $ StaticR ghcjs_allactions_out_js
            addStylesheet $ StaticR css_tree_css
            addStylesheet $ StaticR css_tufte_css
            addStylesheet $ StaticR css_tuftextra_css
            addStylesheet $ StaticR css_exercises_css
            $(widgetFile "default-layout")
            addScript $ StaticR ghcjs_allactions_runmain_js
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")
