module Handler.Chapter where

import Import
import Yesod.Markdown
import Data.List as L (last, tails) 
import Filter.Sidenotes
import Filter.SynCheckers
import Filter.ProofCheckers
import Filter.Translate
import Filter.Diagrams
import Filter.TruthTables
import Text.Pandoc.Walk (walkM, walk)
import System.Directory (doesDirectoryExist, getDirectoryContents, doesFileExist)
import Text.Julius (juliusFile)
import Text.Hamlet (hamletFile)
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import Control.Monad.State (evalState, evalStateT)

-- XXX: Fair amount of code-duplication between this and Handler/Book.hs

getChapterR :: Int -> Handler Html
getChapterR n = do cdirp <- lift $ chapterDir 
                   cdir <- lift $ getDirectoryContents cdirp
                   content <- liftIO $ content n cdir cdirp
                   case content of
                       Right html -> chapterLayout $ layout html
                       Left err -> defaultLayout $ layout (show err)
    where layout c = [whamlet|
                        <div.container>
                            <article>
                                #{c}
                       |]

chapterDir = do localbook <- doesDirectoryExist "book"
                return (if localbook then "book/" else "/root/book/")

content n cdir cdirp = do let matches = filter (\x -> (show n ++ ".pandoc") `elem` tails x) cdir
                          case matches of
                              [] -> do print "no matches"
                                       fileToHtml ""
                              ms  -> do let m = L.last ms 
                                        fileToHtml (cdirp ++ m)

fileToHtml path = do md <- markdownFromFile path
                     case parseMarkdown yesodDefaultReaderOptions md of
                         Right pd -> do pd' <- runFilters pd
                                        return $ Right $ writePandoc yesodDefaultWriterOptions pd'
                         Left e -> return $ Left e

runFilters = let walkNotes y = evalState (walkM makeSideNotes y) 0
                 walkProblems y = walk (makeSynCheckers . makeProofChecker . makeTranslate . makeTruthTables) y
                 walkDiagrams y = evalStateT (walkM makeDiagrams y) []
                   in walkDiagrams . walkNotes . walkProblems

chapterLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        pc <- widgetToPageContent $ do
            toWidgetHead $(juliusFile "templates/command.julius")
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
