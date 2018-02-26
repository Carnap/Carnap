module Handler.Document where

import Import
import Util.Data

getDocumentsR :: Handler Html
getDocumentsR = do publicDocuments <- runDB $ selectList [SharedDocumentScope ==. Public] []
                   pubidents <- mapM (getIdent . sharedDocumentCreator . entityVal) publicDocuments
                   pubmd <- mapM (getUserMD . sharedDocumentCreator . entityVal) publicDocuments
                   muid <- maybeAuthId
                   case muid of
                       Just uid -> do 
                            maybeData <- runDB $ getBy $ UniqueUserData uid
                            case userDataInstructorId <$> entityVal <$> maybeData of 
                               Just id -> do
                                    docs <- runDB $ selectList [SharedDocumentScope ==. InstructorsOnly] []
                                    let privateDocuments = Just docs 
                                    privmd <- mapM (getUserMD . sharedDocumentCreator . entityVal) docs
                                    prividents <- mapM (getIdent . sharedDocumentCreator . entityVal) docs
                                    defaultLayout $ do
                                        setTitle $ "Index of Documents"
                                        $(widgetFile "documentIndex")
                               Nothing -> do let privateDocuments = Nothing
                                                 (privmd, prividents) = ([],[])
                                             defaultLayout $ do
                                                 setTitle $ "Index of Documents"
                                                 $(widgetFile "documentIndex")
                       Nothing -> do let privateDocuments = Nothing
                                         (privmd, prividents) = ([],[])
                                     defaultLayout $ do
                                        setTitle $ "Index of Documents"
                                        $(widgetFile "documentIndex")

getDocumentR :: Text -> Text -> Handler Html
getDocumentR ident title = defaultLayout [whamlet| Nothing yet|]

getIdent uid = do muser <- runDB $ get uid
                  case muser of
                      Just usr -> return $ Just (userIdent usr)
                      Nothing -> return Nothing

getUserMD uid = do mmd <- runDB $ getBy $ UniqueUserData uid
                   case entityVal <$> mmd of
                       Just md -> return $ Just md
                       Nothing -> return Nothing
