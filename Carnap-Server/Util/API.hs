module Util.API where

import Import.NoFoundation
import Crypto.Random (getRandomBytes)
import Data.ByteString.Base64.URL (encode)

generateAPIKey :: HandlerFor app ByteString
generateAPIKey = liftIO (encode <$> getRandomBytes 33)

requireApiKeyFromHeader :: HandlerFor app ByteString
requireApiKeyFromHeader = lookupHeader "X-API-KEY" >>= maybe (sendStatusJSON forbidden403 ("API Key Required" :: Text)) return

