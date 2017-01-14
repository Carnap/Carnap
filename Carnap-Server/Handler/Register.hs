module Handler.Register (getRegisterR,postRegisterR) where

import Import
import Yesod.Form.Bootstrap3

getRegisterR :: Text -> Handler Html
getRegisterR uid = do
    userId <- fromUid uid
    (widget,enctype) <- generateFormPost (registrationForm userId)
    defaultLayout $ do
        setTitle "Carnap - Registration"
        $(widgetFile "register")

postRegisterR uid = do
        userId <- fromUid uid
        ((result,widget),enctype) <- runFormPost (registrationForm userId)
        case result of 
            FormSuccess userdata -> do msuccess <- tryInsert userdata 
                                       if msuccess
                                           then redirect (UserR uid)
                                           else defaultLayout clashPage
            _ -> defaultLayout errorPage

    where errorPage = [whamlet|
                        <div.container>
                            <p> Looks like something went wrong with that form

                            <p>
                                <a href=@{RegisterR uid}>Try again?
                      |]
          clashPage = [whamlet|
                        <div.container>
                            <p> Looks like you're already registered.

                            <p>
                                <a href=@{UserR uid}>Go to your user page?
                      |]

registrationForm :: UserId -> Html -> MForm Handler (FormResult UserData, Widget)
registrationForm userId = do
        renderBootstrap3 BootstrapBasicForm $ fixedId
            <$> areq textField "first name " Nothing
            <*> areq textField "last name " Nothing
            <*> areq (selectFieldList courses) "enrolled in " Nothing
    where fixedId x y z = UserData x y z userId
          courses :: [(Text,Text)]
          courses = [("Symbolic Logic I - Kansas State University","SYM-I-KSU")
                    ,("Birmingham University","BHU" )
                    ]

--This would be a good library function
fromUid uid = runDB $ do (Just (Entity k _)) <- getBy $ UniqueUser uid
                         return k
                    
--this would be a good library function
tryInsert s = runDB $ do munique <- checkUnique s
                         case munique of                  
                              (Just _) -> return False    
                              Nothing  -> do insert s
                                             return True
