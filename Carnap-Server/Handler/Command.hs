module Handler.Command where

import Import
import Carnap.GHCJS.SharedTypes

postCommandR :: Handler Value
postCommandR = do
    EchoBack (s,b) <- (requireJsonBody :: Handler GHCJSCommand)

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just _  -> returnJson (reverse s)
