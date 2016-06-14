module Handler.Chapter where

import Import
import Yesod.Markdown
import System.Directory (getDirectoryContents, doesDirectoryExist)
import Text.Hamlet                 (hamletFile)
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE

getChapterR :: Int -> Handler Html
getChapterR n = do content <- liftIO $ chapter n 
                   case content of
                       Right html -> chapterLayout $ layout html
                       Left err -> defaultLayout $ layout (show err)
    where layout c = [whamlet|
                        <article>
                            #{c}
                       |]

chapter n = do localbook <- doesDirectoryExist "book"
               let path = (if localbook then "book/chapter" else "/root/book/chapter") 
                                    ++  show n ++ ".pandoc"
               fmap markdownToHtml (markdownFromFile path)

chapterLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        pc     <- widgetToPageContent $ do
            addStylesheet $ StaticR css_tufte_css
            $(widgetFile "default-layout")
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")
