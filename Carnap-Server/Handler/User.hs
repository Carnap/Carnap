module Handler.User where

import Import

getUserR :: Text -> Handler Html
getUserR userIdent = do
    defaultLayout $ do
        setTitle "Welcome To Your Homepage!"
        [whamlet|
            <p> Ker boop #{userIdent}
            <a href=@{AuthR LogoutR}>
                Logout
        |]
