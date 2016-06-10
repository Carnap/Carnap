module Handler.Chapter where

import Import
import Yesod.Markdown

getChapterR :: Int -> Handler Html
getChapterR n = do content <- liftIO $ fmap markdownToHtml (markdownFromFile $ "book/chapter" ++ show n ++ ".pandoc")
                   case content of
                       Right html -> defaultLayout $ layout html
                       Left err -> defaultLayout $ layout (show err)
    where layout c = [whamlet|
                        <div class="content">
                            #{c}
                       |]

