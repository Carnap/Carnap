module Handler.Hashed (getHashedR) where

import Import
import System.Directory (doesDirectoryExist)

getHashedR :: Text -> Handler Html
getHashedR s = do localbook <- liftIO $ doesDirectoryExist "book"
                  let path = (if localbook then "book/cache/" else "/root/book/cache/") 
                  sendFile typeSvg (path ++ unpack s)
