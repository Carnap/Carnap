module Handler.Admin where

import Import
import Util.Data
import Util.Database
import Yesod.Form.Bootstrap3
import Yesod.Form.Jquery
import Text.Blaze.Html (toMarkup)
import Data.Time
import System.FilePath
import System.Directory (getDirectoryContents,removeFile, doesFileExist)

getAdminR :: Handler Html
getAdminR = defaultLayout [whamlet|
                                <div.container>
                                    <p> Wecome to Admin
                               |]

