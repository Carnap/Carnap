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
getAdminR = do users <- usersWidget
               defaultLayout [whamlet|
                              <div.container>
                                  <p> Wecome to Admin
                                  ^{users}
                             |]

usersWidget :: HandlerT App IO Widget
usersWidget = do allUserData <- map entityVal <$> (runDB $ selectList [] [])
                 let allUids = (map userDataUserId  allUserData)
                 musers <- mapM (\x -> runDB (get x)) allUids
                 let users = catMaybes musers
                 let usersAndData = zip users allUserData
                 return [whamlet|
                          <div.card style="margin-bottom:20px">
                              <div.card-header>
                                  All Users
                              <div.card-block>
                                  <table.table.table-striped>
                                      <thead>
                                          <th> Identifier
                                          <th> Name
                                      <tbody>
                                          $forall (u,UserData fn ln _ _ _) <- usersAndData
                                              <tr>
                                                  <td>
                                                      <a href=@{UserR (userIdent u)}>#{userIdent u}
                                                  <td>
                                                      #{ln}, #{fn}
                        |]

