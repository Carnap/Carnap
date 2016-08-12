module Handler.Command where

import Import
import Carnap.GHCJS.SharedTypes

postCommandR :: Handler Value
postCommandR = do
    cmd  <- requireJsonBody :: Handler GHCJSCommand

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just _  -> case cmd of
                EchoBack (s,b) -> returnJson (reverse s)
                SubmitSyntaxCheck f -> do returnJson f
                                          
