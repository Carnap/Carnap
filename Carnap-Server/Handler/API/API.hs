module Handler.API.API where

import Import

getAPIR :: Handler Value
getAPIR = returnJson ("v1" :: Text)
