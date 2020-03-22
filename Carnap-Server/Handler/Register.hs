module Handler.Register (getRegisterR, getRegisterEnrollR, getEnrollR, postEnrollR, postRegisterR, postRegisterEnrollR) where

import Import
import Yesod.Form.Bootstrap3
import Util.Database
import Util.Data

getRegister :: ([Entity Course] -> UserId -> Html -> MForm Handler (FormResult (Maybe UserData), Widget)) -> Route App
    -> Text -> Handler Html
getRegister theform theaction ident = do
    userId <- fromIdent ident 
    time <- liftIO getCurrentTime
    courseEntities <- runDB $ selectList [CourseStartDate <. time, CourseEndDate >. time] []
    (widget,enctype) <- generateFormPost (theform courseEntities userId)
    defaultLayout $ do
        setTitle "Carnap - Registration"
        $(widgetFile "register")

postRegister :: ([Entity Course] -> UserId -> Html -> MForm Handler (FormResult (Maybe UserData), Widget)) 
    -> Text -> Handler Html
postRegister theform ident = do
        userId <- fromIdent ident
        time <- liftIO getCurrentTime
        courseEntities <- runDB $ selectList [CourseStartDate <. time, CourseEndDate >. time] []
        ((result,widget),enctype) <- runFormPost (theform courseEntities userId)
        case result of 
            FormSuccess (Just userdata) -> 
                do msuccess <- tryInsert userdata 
                   case msuccess of 
                        Just _ -> do deleteSession "enrolling-in"
                                     redirect (UserR ident)
                        Nothing -> defaultLayout clashPage
            FormSuccess Nothing -> 
                do setMessage "Class not found - link may be incorrect or expired. Please enroll manually."
                   redirect (RegisterR ident)
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

getRegisterR :: Text -> Handler Html
getRegisterR ident = getRegister registrationForm (RegisterR ident) ident

getEnrollR :: Text -> Handler Html
getEnrollR classname = do setSession "enrolling-in" classname
                          (Entity uid user) <- requireAuth
                          ud <- checkUserData uid
                          mclass <- runDB $ getBy (UniqueCourse classname)
                          case (mclass, userDataEnrolledIn ud) of
                              (Just (Entity cid course), Just ecid) -> do 
                                    if cid == ecid then redirect HomeR
                                                   else defaultLayout (reenrollPage cid course user)
                              (Just (Entity cid course), Nothing) -> setMessage "no user data - please restart registration" >> notFound
                              (Nothing,_) -> setMessage "no course with that title" >> notFound
    where reenrollPage cid course user = [whamlet|
                           <div.container>
                               <h2>It looks like you're already enrolled.
                               <p>Do you want to change your enrollment and join #{courseTitle course}?
                               <p>Changing your enrollment will not cause you to lose any saved work.  You can rejoin your previous class by changing your enrollment settings at the bottom of your #
                                  <a href=@{UserR (userIdent user)}>user page#
                                  .
                               <p>
                                   <form action="" method="post">
                                       <button name="change-enrollment" value="change">
                                            Change Enrollment
                         |]

postEnrollR :: Text -> Handler Html
postEnrollR classname = do (Entity uid _) <- requireAuth
                           (mclass, mudent) <- runDB $ (,) <$> getBy (UniqueCourse classname) 
                                                           <*> getBy (UniqueUserData uid)
                           case (mclass, mudent) of
                               (Nothing,_) -> setMessage "no course with that title" >> notFound
                               (_,Nothing) -> setMessage "no user data (do you need to register?)" >> notFound
                               (Just (Entity cid course), Just (Entity udid _)) -> do
                                    runDB $ update udid [UserDataEnrolledIn =. Just cid]
                                    setMessage $ "Enrollment change complete"
                                    redirect HomeR

--registration with enrollment built into the path
getRegisterEnrollR :: Text -> Text -> Handler Html
getRegisterEnrollR theclass ident = getRegister (enrollmentForm theclass) (RegisterEnrollR theclass ident) ident

postRegisterR :: Text -> Handler Html
postRegisterR = postRegister registrationForm

postRegisterEnrollR :: Text -> Text -> Handler Html
postRegisterEnrollR theclass = postRegister (enrollmentForm theclass) 

registrationForm :: [Entity Course] -> UserId -> Html -> MForm Handler (FormResult (Maybe UserData), Widget)
registrationForm courseEntities userId = do
        renderBootstrap3 BootstrapBasicForm $ fixedId
            <$> areq textField "First name " Nothing
            <*> areq textField "Last name " Nothing
            <*> areq (selectFieldList courses) "enrolled in " Nothing
    where fixedId x y z = Just $ UserData x y z Nothing userId 
          courses = ("No Course", Nothing) : map (\e -> (courseTitle $ entityVal e, Just $ entityKey e)) courseEntities 

enrollmentForm :: Text -> [Entity Course] -> UserId -> Html -> MForm Handler (FormResult (Maybe UserData), Widget)
enrollmentForm classtitle courseEntities userId = do
        renderBootstrap3 BootstrapBasicForm $ fixedId
            <$> areq textField "First name " Nothing
            <*> areq textField "Last name " Nothing
    where fixedId x y = case course of 
                    Just c -> Just $ UserData x y (Just c) Nothing userId 
                    Nothing -> Nothing
          course = case filter (\e -> classtitle == courseTitle (entityVal e)) courseEntities of 
                     [] -> Nothing 
                     e:_ -> Just $ entityKey e
