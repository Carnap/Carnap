{-# LANGUAGE DeriveGeneric #-}
module Handler.Admin where

import           Data.Aeson            (encode)
import qualified Data.Text             as T
import           Handler.Instructor    (dateDisplay)
import           Import
import           Settings.Runtime
import           Text.Blaze.Html       (Markup, toMarkup)
import           Text.Julius           (juliusFile)
import           TH.RelativePaths      (pathRelativeToCabalPackage)
import           Util.Data             (jsonSerialize)
import           Yesod.Form.Bootstrap3

deleteAdminR :: Handler Value
deleteAdminR = do
        msg <- requireCheckJsonBody :: Handler DeleteMsg
        case msg of
            DowngradeInstructor uid -> do
                mud <- runDB $ get uid
                case mud of
                    Just ud -> case userDataInstructorId ud of
                                   Just iid -> do runDB $ do cids <- map entityKey <$> selectList [CourseInstructor ==. iid] []
                                                             students <- concat <$> mapM (\cid -> selectList [UserDataEnrolledIn ==. Just cid] []) cids
                                                             mapM_ (\student -> update (entityKey student) [UserDataEnrolledIn =. Nothing]) students
                                                             update uid [UserDataInstructorId =. Nothing]
                                                             deleteCascade iid
                                                  returnJson ("Downgraded!" :: Text)
                                   Nothing -> returnJson ("Not an instructor" :: Text)
                    Nothing -> returnJson ("Instructor doesn't exist?" :: Text)
            LtiDelete key -> do
                runDB $ delete key
                returnJson ("Deleted" :: Text)

formIdUpgrade :: Text
formIdUpgrade = "upgradeToInstructor"

formIdLtiConfig :: Text
formIdLtiConfig = "ltiConfig"

formIdRtSettings :: Text
formIdRtSettings = "rtSettings"

postAdminR :: Handler Html
postAdminR = do
    allUserData <- runDB $ selectList [] []
    let allStudentsData = filter (\x -> userDataInstructorId (entityVal x) == Nothing) allUserData
        allStudentUids = map (userDataUserId . entityVal) allStudentsData
    students <- catMaybes <$> mapM (\x -> runDB (get x)) allStudentUids

    ((upgraderslt,_upgradeWidget),_enctypeUpgrade) <- runFormPost $ identifyForm formIdUpgrade (upgradeToInstructor students)
    ((ltirslt, _), _) <- runFormPost $ identifyForm formIdLtiConfig $ ltiConfigForm
    ((settingsrslt, _), _) <- runFormPost $ identifyForm formIdRtSettings $ rtSettingsSetForm

    checkForm upgraderslt $ \ident -> do
        success <- runDB $ do
            imd <- insert InstructorMetadata
            muent <- getBy $ UniqueUser ident
            mudent <- case entityKey <$> muent of
                          Just uid -> getBy $ UniqueUserData uid
                          Nothing -> return Nothing
            case entityKey <$> mudent of
                 Nothing -> return False
                 Just udid -> do update udid [UserDataInstructorId =. Just imd]
                                 return True
        if success then setMessage $ "user " ++ (toMarkup ident) ++ " upgraded to instructor"
                   else setMessage $ "couldn't upgrade user " ++ (toMarkup ident) ++ " to instructor"

    checkForm ltirslt $ \(iss, cid, oidcEndp, jwksUrl) -> do
        --we strip leading and terminal whitespace from URLS before insert
        runDB $ insert_ $ LtiPlatformInfo (T.strip iss) (T.strip cid) (T.strip oidcEndp) (T.unpack (T.strip jwksUrl))
        setMessage $  "Successfully added LTI platform with CID " ++ toMarkup cid

    checkForm settingsrslt $ \rts -> do
        runDB $ setRtSetting rts

    redirect AdminR --XXX: redirect here to make sure changes are visually reflected

    where
        showFailure s = setMessage $ "Something went wrong: " ++ toMarkup (show s)
        checkForm res act = case res of
            FormSuccess v -> act v
            FormFailure s -> showFailure s
            FormMissing   -> return ()

getAdminR :: Handler Html
getAdminR = do allUserData <- runDB $ selectList [] []
               let allInstructorsData = filter (\x -> userDataInstructorId (entityVal x) /= Nothing) allUserData
                   allStudentsData = filter (\x -> userDataInstructorId (entityVal x) == Nothing) allUserData
                   allInstructorUids = map (userDataUserId .entityVal)  allInstructorsData
                   allStudentUids = map (userDataUserId . entityVal) allStudentsData
               allCoursesByInstructor <- mapM getCoursesWithEnrollment (map entityVal allInstructorsData)
               allInstructors <- catMaybes <$> mapM (\x -> runDB (get x)) allInstructorUids
               let instructorsPlus = zip3 allInstructors allInstructorsData allCoursesByInstructor
               students <- catMaybes <$> mapM (\x -> runDB (get x)) allStudentUids
               instructorW <- instructorWidget instructorsPlus
               emailW <- emailWidget allInstructors
               unenrolledW <- unenrolledWidget allStudentsData (concat allCoursesByInstructor)

               rtSettingsW <- rtSettingsWidget
               (rtSettingsForm, enctypeRtSetting) <- generateFormPost (identifyForm formIdRtSettings rtSettingsSetForm)

               (upgradeWidget,enctypeUpgrade) <- generateFormPost (identifyForm formIdUpgrade $ upgradeToInstructor students)
               (ltiWidget,enctypeLti) <- generateFormPost (identifyForm formIdLtiConfig $ ltiConfigForm)
               ltiConfigsW <- ltiConfigsWidget
               defaultLayout $ do
                   toWidgetHead $(juliusFile =<< pathRelativeToCabalPackage "templates/admin.julius")
                   [whamlet|
                    <div.container>
                        <h1> Admin Portal
                        ^{emailW}
                        ^{instructorW}
                        ^{unenrolledW}
                        <form method=post enctype=#{enctypeUpgrade}>
                            ^{upgradeWidget}
                             <div.form-group>
                                 <input.btn.btn-primary type=submit value="Upgrade Instructor">
                        <hr>
                        ^{rtSettingsW}
                        <form method=post enctype=#{enctypeRtSetting}>
                            ^{rtSettingsForm}
                            <div.form-group>
                                <input.btn.btn-primary type=submit value="Set">
                        <hr>
                        <h3> LTI 1.3 Configuration
                        <form method="post" enctype=#{enctypeLti}>
                            ^{ltiWidget}
                            <div.form-group>
                                <input.btn.btn-primary type=submit value="Create new platform">
                        ^{ltiConfigsW}
                   |]

getAdminPromoteR :: Handler Html
getAdminPromoteR =
    do aid <- maybeAuthId >>= maybe (permissionDenied "not logged in") return
       (promoteW, enctypePromote) <- generateFormPost $ promoteToAdmin (show aid)
       defaultLayout $ do
           [whamlet|
            <div.container>
                <h1> Become an administrator
                <form method=post enctype=#{enctypePromote}>
                    ^{promoteW}
                    <div.form-group>
                        <input.btn.btn-primary type=submit value="Promote me">
           |]

promoteToAdmin
    :: String -> Markup -> MForm (HandlerFor App) (FormResult String, WidgetFor App ())
promoteToAdmin ident = renderBootstrap3 BootstrapBasicForm $
        areq userId "" (Just ident)
    where userId = hiddenField

postAdminPromoteR :: Handler Html
postAdminPromoteR =
    do aid <- maybeAuthId >>= maybe (permissionDenied "not logged in") return
       ((promoteResult, _), _) <- runFormPost $ promoteToAdmin (show aid)
       case readMay <$> promoteResult of
            FormSuccess (Just uid) -> do
               userdata <- runDB $ getBy $ UniqueUserData uid
               case userdata of
                    Just (Entity key _) -> do
                        runDB $ update key [UserDataIsAdmin =. True]
                        defaultLayout $ [whamlet|
                             Congratulations! You've been promoted. You can now #
                             <a href=@{AdminR}>manage the site
                        |]
                    Nothing -> permissionDenied "User data missing. This may mean you haven't assigned yourself a name yet."
            _ -> invalidArgs ["form failed"]

upgradeToInstructor :: [User] -> Html -> MForm (HandlerFor App) (FormResult Text, WidgetFor App ())
upgradeToInstructor users = renderBootstrap3 BootstrapBasicForm $
                                areq (selectFieldList userIdents) (bfs ("Upgrade User to Instructor" :: Text)) Nothing
        where userIdents = let idents = map userIdent users in zip idents idents

unenrolledWidget :: [Entity UserData] -> [(Entity Course,[Entity UserData])] -> HandlerFor App Widget
unenrolledWidget students courses = do
       time <- liftIO getCurrentTime
       let unenrolledData = filter (\x -> userDataEnrolledIn (entityVal x) == Nothing) students
           inactive = filter (\(c,_) -> courseEndDate (entityVal c) < time)
           expiredData = concat . map snd . inactive $ courses
       unenrolled <- catMaybes <$> mapM (\ud -> runDB $ get (userDataUserId (entityVal ud))) unenrolledData
       expired <- catMaybes <$> mapM (\ud -> runDB $ get (userDataUserId (entityVal ud))) expiredData
       return [whamlet|
            <div.card style="margin-bottom:20px">
                <div.card-header> Unenrolled and Expired Students
                <div.card-block>
                  <table.table.table-striped>
                        <thead>
                            <th> Ident
                            <th> Name
                        <tbody>
                            $forall (User ident _, Entity _ (UserData {userDataFirstName = fn, userDataLastName = ln})) <- zip unenrolled unenrolledData

                                <tr>
                                    <td>
                                        <a href=@{UserR ident}>#{ident}
                                    <td>
                                        #{ln}, #{fn}
                        <tbody>
                            $forall (User ident _, Entity _ (UserData {userDataFirstName = fn, userDataLastName = ln})) <- zip expired expiredData

                                <tr>
                                    <td>
                                        <a href=@{UserR ident}>#{ident}
                                    <td>
                                        #{ln}, #{fn}
            |]

emailWidget :: [User] -> HandlerFor App Widget
emailWidget insts = do let emails = intercalate "," (map userIdent insts)
                       return [whamlet|
                          <a href="mailto:gleachkr@gmail.com?bcc=#{emails}">Email Instructors
                       |]

instructorWidget :: [(User,Entity UserData,[(Entity Course,[Entity UserData])])] -> HandlerFor App Widget
instructorWidget instructorPlus =
        do time <- liftIO getCurrentTime
           let active = filter (\(c,_) -> courseEndDate (entityVal c) > time)
               inactive = filter (\(c,_) -> courseEndDate (entityVal c) < time)
           return [whamlet|
                 $forall (instructor, Entity key (UserData {userDataFirstName = fn, userDataLastName = ln}), courses) <- instructorPlus
                     <div.card style="margin-bottom:20px">
                         <div.card-header>
                             <a href=@{UserR (userIdent instructor)}>#{userIdent instructor}
                             — #{fn} #{ln}
                         <div.card-block>
                               $forall (course, enrollment) <- active courses
                                   <h3> #{courseTitle (entityVal course)}
                                   <table.table.table-striped>
                                     <thead>
                                         <th> Name
                                     <tbody>
                                         $forall UserData {userDataFirstName = sfn, userDataLastName = sln} <- map entityVal enrollment
                                             <tr>
                                                 <td>
                                                     #{sln}, #{sfn}
                               $if null $ inactive courses
                               $else
                                   <h3>Inactive Classes
                                   <table.table.table-striped>
                                     <thead>
                                       <th> Name
                                       <th> End Date
                                     <tbody>
                                       $forall (course, _) <- inactive courses
                                         <tr>
                                             <td> #{courseTitle (entityVal course)}
                                             <td> #{dateDisplay (courseEndDate (entityVal course)) (entityVal course)}
                             <button.btn.btn-sm.btn-danger type="button" onclick="tryDelete('#{userIdent instructor}', '#{decodeUtf8 $ encode $ DowngradeInstructor key}')">
                                 Downgrade Instructor
           |]

rtSettingsWidget :: HandlerFor App Widget
rtSettingsWidget = do
    settings <- runDB getRtSettings
    return [whamlet|
        <h3> Site Configuration
        <table.table.table-striped>
            <thead>
                <th> Setting
            <tbody>
                $forall set <- settings
                    <tr><td> #{show set}
    |]

-- | a text field with no default value
reqTextField :: Text -> AForm (HandlerFor App) Text
reqTextField name = areq textField (bfs name) Nothing

fieldName :: Text -> FieldSettings site
fieldName = bfs

rtSettingsSetForm :: Html -> MForm (HandlerFor App) (FormResult RTSetting, WidgetFor App ())
rtSettingsSetForm = renderBootstrap3 BootstrapBasicForm $ wFormToAForm $ do
    let settingsList = tshow <$> enumFrom TyDisableGoogleReg
        settingsList' = zip (removePrefix "Ty" <$> settingsList) settingsList

    which <- wreq (selectFieldList settingsList') (fieldName "Setting") Nothing
    wreq (settingsField which) (fieldName "Value (JSON)") Nothing

    where
        settingsField ty = Field
            { fieldParse = parseHelper (parseSettingsField ty)
            , fieldView = \theId name attrs _val isReq ->
                [whamlet|
                    $newline never
                    <input id="#{theId}" name="#{name}" *{attrs} type="text" :isReq:required>
                |]
            , fieldEnctype = UrlEncoded
            }

        parseSettingsField (FormSuccess ty) t = maybe (Left $ MsgInvalidEntry "Parse failure") Right $ toSetting ty t
        parseSettingsField _ _ = Left . MsgInvalidEntry $ "Selected setting missing or bad"

        toSetting :: Text -> Text -> Maybe RTSetting
        toSetting name val =
            ((parseRtSetting `flip` (encodeUtf8 val)) =<< readMay name)

        -- | remove prefix, returning the existing string if it's not present
        removePrefix prefix s = fromMaybe s $ stripPrefix prefix s


getCoursesWithEnrollment :: UserData -> HandlerFor App [(Entity Course, [Entity UserData])]
getCoursesWithEnrollment ud =
    case userDataInstructorId ud of
        Just iid -> do courseEnt <- runDB $ selectList [CourseInstructor ==. iid] []
                       enrollments <- mapM (\c -> runDB $ selectList [UserDataEnrolledIn ==. Just (entityKey c)] []) courseEnt
                       return $ zip courseEnt enrollments

        Nothing -> return []

ltiConfigForm :: Html -> MForm (HandlerFor App) (FormResult (Text, Text, Text, Text), WidgetFor App ())
ltiConfigForm = renderBootstrap3 BootstrapBasicForm $ (,,,)
    <$> reqTextField "Issuer"
    <*> reqTextField "client_id"
    <*> reqTextField "OIDC Auth Endpoint"
    <*> reqTextField "JWKs URL"

ltiConfigsWidget :: HandlerFor App Widget
ltiConfigsWidget = do
    ltiConfigs <- runDB $ selectList ([] :: [Filter LtiPlatformInfo]) []
    return [whamlet|
            <h4>Configured LTI Platforms
            <table.table.table-striped>
                <thead>
                    <th> iss
                    <th> client_id
                    <th> OIDC Auth Endpoint
                    <th> JWK URL
                    <th> Actions
                <tbody>
                    $forall Entity k (LtiPlatformInfo iss cid endpoint jwksUrl) <- ltiConfigs
                        <tr>
                            <td> #{iss}
                            <td> #{cid}
                            <td> #{endpoint}
                            <td> #{jwksUrl}
                            <td>
                                <button.btn.btn-sm.btn-secondary type="button" alt="edit"
                                    title="Delete" onclick="ltiDelete('#{jsonSerialize $ LtiDelete k}')">
                                    <i.fa.fa-trash-o>
        |]

data DeleteMsg = DowngradeInstructor UserDataId
               | LtiDelete (Key LtiPlatformInfo)
    deriving Generic

instance ToJSON DeleteMsg
instance FromJSON DeleteMsg

