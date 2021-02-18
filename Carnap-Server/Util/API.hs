module Util.API where

import Import.NoFoundation
import Crypto.Random (getRandomBytes)
import Data.ByteString.Base64.URL (encode)

generateAPIKey :: HandlerFor app ByteString
generateAPIKey = liftIO (encode <$> getRandomBytes 33)

getAPIKeyFromHeader :: HandlerFor app (Maybe ByteString)
getAPIKeyFromHeader = lookupHeader "X-API-KEY"

requireAPIKeyFromHeader :: HandlerFor app ByteString
requireAPIKeyFromHeader = getAPIKeyFromHeader >>= maybe (sendStatusJSON forbidden403 ("API Key Required" :: Text)) return
