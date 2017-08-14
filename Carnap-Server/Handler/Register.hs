module Handler.Register (getRegisterR,postRegisterR) where

import Import
import Yesod.Form.Bootstrap3
import Util.Database
import Util.Data

getRegisterR :: Text -> Handler Html
getRegisterR ident = do
    userId <- fromIdent ident 
    (widget,enctype) <- generateFormPost (registrationForm userId)
    defaultLayout $ do
        setTitle "Carnap - Registration"
        $(widgetFile "register")

postRegisterR ident = do
        userId <- fromIdent ident
        ((result,widget),enctype) <- runFormPost (registrationForm userId)
        case result of 
            FormSuccess userdata -> do msuccess <- tryInsert userdata 
                                       if msuccess
                                           then redirect (UserR ident)
                                           else defaultLayout clashPage
            _ -> defaultLayout errorPage

    where errorPage = [whamlet|
                        <div.container>
                            <p> Looks like something went wrong with that form

                            <p>
                                <a href=@{RegisterR ident}>Try again?
                      |]
          clashPage = [whamlet|
                        <div.container>
                            <p> Looks like you're already registered.

                            <p>
                                <a href=@{UserR ident}>Go to your user page?
                      |]

registrationForm :: UserId -> Html -> MForm Handler (FormResult UserData, Widget)
registrationForm userId = do
        renderBootstrap3 BootstrapBasicForm $ fixedId
            <$> areq textField "first name " Nothing
            <*> areq textField "last name " Nothing
            <*> areq (selectFieldList courses) "enrolled in " Nothing
    where fixedId x y z = UserData x y z userId
          courses :: [(Text,CourseEnrollment)]
          courses = [("Symbolic Logic I - Kansas State University",KSUSymbolicI2017)
                    ,("Introduction to Formal Logic - Kansas State University", KSUIntroToFormal2017)
                    ,("Birmingham University",Birmingham2017 )
                    ]
