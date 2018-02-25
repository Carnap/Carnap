module Handler.Document where

import Import
import Util.Data

getDocumentsR :: Handler Html
getDocumentsR = do publicDocuments <- runDB $ selectList [SharedDocumentScope ==. Public] []
                   muid <- maybeAuthId
                   case muid of
                       Just uid -> do 
                            maybeData <- runDB $ getBy $ UniqueUserData uid
                            case userDataInstructorId <$> entityVal <$> maybeData of 
                               Just id -> do
                                    docs <- runDB $ selectList [SharedDocumentScope ==. InstructorsOnly] []
                                    let privateDocuments = Just docs 
                                    defaultLayout $ do
                                        setTitle $ "Index of Documents"
                                        $(widgetFile "documentIndex")
                               Nothing -> do let privateDocuments = Nothing
                                             defaultLayout $ do
                                                 setTitle $ "Index of Documents"
                                                 $(widgetFile "documentIndex")
                       Nothing -> do let privateDocuments = Nothing
                                     defaultLayout $ do
                                        setTitle $ "Index of Documents"
                                        $(widgetFile "documentIndex")

getDocumentR :: Text -> Text -> Handler Html
getDocumentR ident title = defaultLayout [whamlet| Nothing yet|]
