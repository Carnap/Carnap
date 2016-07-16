module Handler.Home where

import Import

-- This is a handler function for the GET request method on the HomeR
-- resource pattern. All of your resource patterns are defined in
-- config/routes
--
-- The majority of the code you will write in Yesod lives in these handler
-- functions. You can spread them across multiple files if you are so
-- inclined, or create a single monolithic file.
getHomeR :: Handler Html
getHomeR = do
    defaultLayout $ do
        aDomId <- newIdent
        addScript $ StaticR ghcjs_rts_js
        addScript $ StaticR ghcjs_syncheck_lib_js
        addScript $ StaticR ghcjs_syncheck_out_js
        setTitle "Welcome To Carnap!"
        $(widgetFile "homepage")
        $(widgetFile "command")
        $(fayFile "Home")
        $(fayFile "Comment")
        addScript $ StaticR ghcjs_syncheck_runmain_js
