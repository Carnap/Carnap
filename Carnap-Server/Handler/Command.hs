module Handler.Command where

import Import

postCommandR :: Handler Value
postCommandR = do
    command <- (requireJsonBody :: Handler String)

    maybeCurrentUserId <- maybeAuthId

    returnJson (reverse command)

