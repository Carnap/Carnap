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
getAdminR = do allUserData <- map entityVal <$> (runDB $ selectList [] [])
               let allUids = (map userDataUserId  allUserData)
               musers <- mapM (\x -> runDB (get x)) allUids
               let users = catMaybes musers
               usertable <- usersWidget users allUserData
               (upgradeWidget,enctypeUpgrade) <- generateFormPost (upgradeToInstructor users)
               defaultLayout [whamlet|
                              <div.container>
                                  <p> Wecome to Admin
                                  ^{usertable}
                                  <form method=post enctype=#{enctypeUpgrade}>
                                      ^{upgradeWidget}
                                       <div.form-group>
                                           <input.btn.btn-primary type=submit value="upgrade">
                             |]

upgradeToInstructor users = renderBootstrap3 BootstrapBasicForm $
                                areq (selectFieldList userIdents) (bfs ("Upgrade User to Instructor" :: Text)) Nothing
        where userIdents = let idents = map userIdent users in zip idents idents

usersWidget :: [User] -> [UserData] -> HandlerT App IO Widget
usersWidget us ud = do let usersAndData = zip us ud
                       return [whamlet|
                                  <div.card style="margin-bottom:20px">
                                      <div.card-header>
                                          All Users
                                      <div.card-block>
                                          <table.table.table-striped>
                                              <thead>
                                                  <th> Identifier
                                                  <th> Name
                                                  <th> Instructor?
                                              <tbody>
                                                  $forall (u,UserData fn ln _ mid _) <- usersAndData
                                                      <tr>
                                                          <td>
                                                              <a href=@{UserR (userIdent u)}>#{userIdent u}
                                                          <td>
                                                              #{ln}, #{fn}
                                                          $maybe _ <- mid
                                                              <td>yes
                                                          $nothing
                                                              <td>no

                        |]

