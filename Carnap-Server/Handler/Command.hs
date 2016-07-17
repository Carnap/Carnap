module Handler.Command where

import Import

postCommandR :: Handler Value
postCommandR = do
    (s1, s2) <- (requireJsonBody :: Handler (String,String))

    maybeCurrentUserId <- maybeAuthId

    returnJson (reverse s1)

