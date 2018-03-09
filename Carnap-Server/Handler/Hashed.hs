module Handler.Hashed (getHashedR) where

import Import
import System.Directory (doesDirectoryExist)

getHashedR :: Text -> Handler Html
getHashedR s = do bookdir <- appBookRoot <$> (appSettings <$> getYesod)
                  let path = bookdir </> "cache/"
                  sendFile typeSvg (path ++ unpack s)
