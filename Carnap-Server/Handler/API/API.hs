{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
module Handler.API.API where

import Import
import Util.Database (maybeAPIIdent)

data APISelfResponse = APISelfResponse
    { version :: Text
    , ident   :: Text
    } deriving (Show, Generic)

instance ToJSON APISelfResponse

getAPIR :: Handler Value
getAPIR = do
    ident <- maybe
        (sendStatusJSON forbidden403 ("calling user has no user data" :: Text)) pure
        =<< maybeAPIIdent
    returnJson $ APISelfResponse { version = "v1", ident = ident }
