module Handler.Hashed (getHashedR) where

import Import
import System.Directory (doesDirectoryExist)

getHashedR :: Text -> Handler Html
getHashedR s = do datadir <- appDataRoot <$> (appSettings <$> getYesod)
                  let path = datadir </> "book/cache/"
                  sendFile typeSvg (path ++ unpack s)
