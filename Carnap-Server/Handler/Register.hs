module Handler.Register (getRegisterR,postRegisterR) where

import Import
import Yesod.Form.Bootstrap3
import Util.Database
import Util.Data

getRegisterR :: Text -> Handler Html
getRegisterR ident = do
    userId <- fromIdent ident 
    (widget,enctype) <- generateFormPost (registrationForm userId (SandboxCourse <$> instructorByEmail ident))
    defaultLayout $ do
        setTitle "Carnap - Registration"
        $(widgetFile "register")

postRegisterR ident = do
        userId <- fromIdent ident
        ((result,widget),enctype) <- runFormPost (registrationForm userId (SandboxCourse <$> instructorByEmail ident))
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

registrationForm :: UserId -> Maybe CourseEnrollment -> Html -> MForm Handler (FormResult UserData, Widget)
registrationForm userId maybeSandbox = do
        renderBootstrap3 BootstrapBasicForm $ fixedId
            <$> areq textField "first name " Nothing
            <*> areq textField "last name " Nothing
            <*> areq (selectFieldList courses) "enrolled in " Nothing
    where fixedId x y z = UserData x y z Nothing userId 
          courses = map (\c -> (nameOf $ courseData c, c)) $
                        case maybeSandbox of 
                            Just sb ->  sb:regularCourseList 
                            Nothing ->  regularCourseList
