module Handler.Command where

import Import

postCommandR :: Handler Value
postCommandR = do
    (s1, s2) <- (requireJsonBody :: Handler (String,Bool))

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just _  -> returnJson (reverse s1)
