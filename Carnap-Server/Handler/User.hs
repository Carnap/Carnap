{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
module Handler.User where

import Import
import Text.Read (readMaybe)
import qualified Text.Blaze.Html5 as B
import Carnap.GHCJS.SharedTypes
import Yesod.Form.Bootstrap3
import Data.Time
import Data.List ((!!),elemIndex)
import Data.Time.Zones
import Data.Time.Zones.All
import Util.Data
import Util.Database
import Util.Grades
import qualified Data.IntMap as IM
import Data.IntMap ((!))

postUserR :: Text -> Handler Html
postUserR ident = do
    musr <- runDB $ getBy $ UniqueUser ident
    case musr of
        Nothing -> defaultLayout nouserPage
        (Just (Entity uid _))  -> do
            ud <- checkUserData uid
            when (userDataIsLti ud) $ invalidArgs ["LTI users cannot update their data"]
            time <- liftIO getCurrentTime
            classes <- runDB $ selectList [CourseStartDate <. time, CourseEndDate >. time] []
            ((updateRslt,_),_) <- runFormPost (identifyForm "updateInfo" $ updateUserDataForm ud classes)
            ((dropRslt,_),_) <- runFormPost (identifyForm "dropClass" $ dropClassForm)
            case updateRslt of
                 FormFailure s -> setMessage $ "Something went wrong with updating your information: " ++ B.toMarkup (show s)
                 FormMissing -> return ()
                 FormSuccess (mc, fn , ln, uniid) -> runDB $ do
                         mudent <- getBy $ UniqueUserData uid
                         case entityKey <$> mudent of
                               Nothing -> setMessage "No user data to update."
                               Just udid -> do
                                    case mc of
                                        Nothing -> update udid [ UserDataFirstName =. fn
                                                              , UserDataLastName =. ln
                                                              , UserDataUniversityId =. uniid]
                                        Just c -> update udid [ UserDataFirstName =. fn
                                                              , UserDataLastName =. ln
                                                              , UserDataUniversityId =. uniid
                                                              , UserDataEnrolledIn =. (Just $ entityKey c)]
                                    return ()
            case dropRslt of
                 FormMissing -> return ()
                 FormFailure s -> setMessage $ "Something went wrong with dropping the class: " ++ B.toMarkup (show s)
                 FormSuccess () -> runDB $ do
                         mudent <- getBy $ UniqueUserData uid
                         case entityKey <$> mudent of
                               Nothing -> setMessage "No user data to drop class." 
                               Just udid -> update udid [UserDataEnrolledIn =. Nothing]
                         return ()
            redirect (UserR ident)--XXX: redirect here to make sure changes are visually reflected

deleteUserR :: Text -> Handler Value
deleteUserR _ = do
    msg <- requireCheckJsonBody :: Handler Text
    maybeCurrentUserId <- maybeAuthId
    case maybeCurrentUserId of
        Nothing -> return ()
        Just u -> runDB $ do kl <- selectKeysList [SavedDerivedRuleUserId ==. u ,SavedDerivedRuleName ==. msg ] []
                             kl' <- selectKeysList [SavedRuleUserId ==. u,SavedRuleName ==. msg ] []
                             case kl of [] -> return (); k:_ -> delete k
                             case kl' of [] -> return (); k:_ -> delete k
    returnJson (msg ++ " deleted")

getUserR :: Text -> Handler Html
getUserR ident = do
    musr <- runDB $ getBy $ UniqueUser ident
    case musr of
        Nothing -> defaultLayout nouserPage
        (Just (Entity uid _))  -> do
            ud@UserData 
                { userDataEnrolledIn = maybeCourseId
                , userDataInstructorId = maybeInstructorId
                , userDataFirstName = firstname
                , userDataLastName = lastname
                , userDataIsLti
                } <- checkUserData uid
            time <- liftIO getCurrentTime
            (dropForm,encTypeDrop) <- generateFormPost (identifyForm "dropClass" $ dropClassForm)
            let isInstructor = case maybeInstructorId of Just _ -> True; _ -> False
            derivedRulesOld <- getDerivedRules uid
            derivedRulesNew <- getRules uid
            maybeCourse <- case maybeCourseId of
                              Just cid -> do runDB $ get cid
                              Nothing  -> return Nothing
            case maybeCourse of
                Just course -> do
                    (updateForm,encTypeUpdate) <- generateFormPost (identifyForm "updateInfo" $ updateUserDataForm ud [])
                    -- safety: `Nothing` case unreachable since `maybeCourse` will be `Nothing` also
                    let Just cid = maybeCourseId
                    textbookproblems <- getProblemSets cid
                    (asmd, extensions, asDocs,accommodation,subs) <- runDB $ 
                            do asmd <-  selectList [AssignmentMetadataCourse ==. cid] []
                               asDocs <- mapM get (map (assignmentMetadataDocument . entityVal) asmd)
                               accommodation <- (getBy $ UniqueAccommodation cid uid)
                                            >>= return . maybe 0 (accommodationDateExtraHours . entityVal)
                               extensions <- mapM (\asgn -> getBy $ UniqueExtension (entityKey asgn) uid) asmd 
                               let pq = problemQuery uid (map entityKey asmd) 
                               subs <- map entityVal <$> selectList pq []
                               return (asmd, extensions,asDocs,accommodation,subs)
                    assignments <- assignmentsOf accommodation course textbookproblems (zip asmd extensions) asDocs
                    subtable <- problemsToTable course accommodation textbookproblems (zip asmd extensions) asDocs subs
                    defaultLayout $ do
                        addScript $ StaticR js_bootstrap_bundle_min_js
                        addScript $ StaticR js_bootstrap_min_js
                        setTitle "Welcome To Your Homepage!"
                        $(widgetFile "user")
                Nothing -> do
                    classes <- runDB $ selectList [CourseStartDate <. time, CourseEndDate >. time] []
                    (updateForm,encTypeUpdate) <- generateFormPost (identifyForm "updateInfo" $ updateUserDataForm ud classes)
                    defaultLayout $ do
                                addScript $ StaticR js_bootstrap_bundle_min_js
                                addScript $ StaticR js_bootstrap_min_js
                                [whamlet|
                                <div.container>
                                    ^{updateWidget updateForm encTypeUpdate}
                                    <p> You are not currently enrolled in any class. You can enroll in a class by editing your personal information, below.
                                    $if isInstructor
                                        <p> Your instructor page is #
                                            <a href=@{InstructorR ident}>here

                                    <div.card>
                                        <div.card-header> Personal Information
                                        <div.card-block>
                                            ^{personalInfo ud Nothing}
                                    <a href=@{AuthR LogoutR}>
                                        Logout
                               |]

getUserDispatchR :: Handler Html
getUserDispatchR = maybeAuthId
                   >>= maybe (redirect HomeR)
                             (getIdent >=> maybe (redirect HomeR) goHome)
    where goHome ident = do mid <- instructorIdByIdent ident
                            case mid of
                              Nothing -> redirect $ UserR ident
                              Just _ -> redirect $ InstructorR ident

--------------------------------------------------------
--Due dates
--------------------------------------------------------
--functions for dealing with time and due dates

dateDisplay :: UTCTime -> Course -> String
dateDisplay inUtc course = case tzByName $ courseTimeZone course of
                             Just tz  -> formatTime defaultTimeLocale "%F %R %Z" $ utcToZonedTime (timeZoneForUTCTime tz inUtc) inUtc
                             Nothing -> formatTime defaultTimeLocale "%F %R UTC" $ utc

--------------------------------------------------------
--Components
--------------------------------------------------------
--reusable components
problemsToTable :: Course -> Int -> Maybe BookAssignmentTable 
    -> [(Entity AssignmentMetadata, Maybe (Entity Extension))] -> [Maybe Document] -> [ProblemSubmission] 
    -> HandlerFor App Html
problemsToTable course accommodation textbookproblems asmdex asDocs submissions = do
            time <- liftIO getCurrentTime
            rows <- mapM (toRow time) submissions
            withUrlRenderer [hamlet|
                                    $forall row <- rows
                                        ^{row}|]
        where asmd = map fst asmdex
              toRow time p = do let score = if isReleased time (problemSubmissionSource p)
                                             then show $ toScoreAny textbookproblems asmdex accommodation p
                                             else "-"
                                return [hamlet|
                                  <tr>
                                    <td>^{printSource (problemSubmissionSource p)}
                                    <td>#{problemSubmissionIdent p}
                                    <td title="#{displayProblemData $ problemSubmissionData p}">
                                        <div.problem-display> #{displayProblemData $ problemSubmissionData p}
                                    <td>#{dateDisplay (problemSubmissionTime p) course}
                                    <td.score-column>#{score}
                                    <td>#{show $ problemSubmissionType p}|]

              isReleased _ Book = True
              isReleased time (Assignment s) = 
                case readMaybe s 
                        >>= (\k -> headMay $ filter (\md -> entityKey md == k) asmd)
                        >>= assignmentMetadataGradeRelease . entityVal
                        of Nothing -> True
                           Just d -> time `laterThan` d

              printSource Book = [hamlet|Textbook|]
              printSource (Assignment s) = 
                case (readMaybe s) of
                    Nothing -> [hamlet|Unknown|]
                    Just k -> case elemIndex k (map entityKey asmd) of
                            Nothing -> [hamlet|No existing assignment|]
                            Just n -> case asDocs !! n of
                                Nothing -> [hamlet|No document|]
                                Just d -> [hamlet| <a href=@{CourseAssignmentR (courseTitle course) (documentFilename d)}>#{documentFilename d}|]

tryDelete :: (Semigroup a, IsString a) => a -> a
tryDelete name = "tryDeleteRule(\"" <> name <> "\")"

--properly localized assignments for a given class XXX---should this just be in the hamlet?
assignmentsOf :: Int -> Course -> Maybe BookAssignmentTable -> [(Entity AssignmentMetadata, Maybe (Entity Extension))] -> [Maybe Document] 
    -> HandlerFor App (WidgetFor App ())
assignmentsOf accommodation course textbookproblems asmdex asDocs = do
             time <- liftIO getCurrentTime
             return $
                [whamlet|
                <div.table-responsive>
                    <table.table.table-striped>
                        <thead>
                            <th> Assignment
                            <th> Due Date
                            <th> Description
                        <tbody>
                            $maybe dd <- textbookproblems
                                $forall (num,due) <- IM.toList (readAssignmentTable dd)
                                    <tr>
                                        <td>
                                            <a href=@{ChapterR $ chapterOfProblemSet ! num}>
                                                Problem Set #{show num}
                                        <td>
                                            #{dateDisplay (addUTCTime accommodationUTC due) course}
                                        <td>
                            $forall ((Entity _ a,mex), Just d) <- zip asmdex asDocs
                                $if visibleAt time a mex
                                        <tr>
                                            <td>
                                                <a href=@{CourseAssignmentR (courseTitle course) (documentFilename d)}>
                                                    #{documentFilename d}
                                            $maybe (Entity _ ex) <- mex
                                                $maybe due <- assignmentMetadataDuedate a
                                                    <td>
                                                        <s>#{dateDisplay (addUTCTime accommodationUTC due) course}
                                                        <em>#{dateDisplay (extensionUntil ex) course}
                                                $nothing
                                                    <td>
                                                        <em>#{dateDisplay (extensionUntil ex) course}
                                            $nothing
                                                $maybe due <- assignmentMetadataDuedate a
                                                    <td>#{dateDisplay (addUTCTime accommodationUTC due) course}
                                                $nothing
                                                    <td>No Due Date
                                            $maybe desc <- assignmentMetadataDescription a
                                                <td>
                                                    <div.assignment-desc>#{desc}
                                            $nothing
                                                <td>-
                |]
    where accommodationUTC = fromIntegral (3600 * accommodation) :: NominalDiffTime
          visibleAt t a mex = not (hidden a) && not (tooEarly t a) && not (tooLate t a mex)
          hidden = maybe False availabilityHidden . assignmentMetadataAvailability
          tooEarly t a | null (assignmentMetadataVisibleFrom a) = False
                       | otherwise = Just t < assignmentMetadataVisibleFrom a
          tooLate t a _ | null (assignmentMetadataVisibleTill a) = False
          tooLate t a Nothing = assignmentMetadataVisibleTill a < Just t
          tooLate t a (Just (Entity _ ex)) = (extensionUntil ex < t) && (assignmentMetadataVisibleTill a < Just t)

updateWidget :: WidgetFor App () -> Enctype -> WidgetFor App ()
updateWidget form enc = [whamlet|
                    <div class="modal fade" id="updateUserData" tabindex="-1" role="dialog" aria-labelledby="updateUserDataLabel" aria-hidden="true">
                        <div class="modal-dialog" role="document">
                            <div class="modal-content">
                                <div class="modal-header">
                                    <h5 class="modal-title" id="updateUserDataLabel">Update User Data</h5>
                                    <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                      <span aria-hidden="true">&times;</span>
                                <div class="modal-body">
                                    <form method=post enctype=#{enc}>
                                        ^{form}
                                        <div.form-group>
                                            <input.btn.btn-primary type=submit value="update">
                    |]

dropWidget :: WidgetFor App () -> Enctype -> WidgetFor App ()
dropWidget form enc = [whamlet|
                        <form id="drop-class" style="display:inline-block" method=post enctype=#{enc}>
                            ^{form}
                            <div.form-group>
                                <input.btn.btn-primary type=submit value="Unenroll">
                      |]

personalInfo :: UserData -> Maybe Course -> WidgetFor site ()
personalInfo (UserData {userDataUniversityId = muniversityid,
                        userDataFirstName = firstname, userDataLastName = lastname,
                        userDataIsLti = isLti }) mcourse
    = [whamlet|
        <dl.row>
            <dt.col-sm-3>First Name
            <dd.col-sm-9>#{firstname}
            <dt.col-sm-3>Last Name
            <dd.col-sm-9>#{lastname}
            $maybe course <- mcourse
                <dt.col-sm-3>Course Enrollment
                <dd.col-sm-9>#{courseTitle course}
                $maybe desc <- courseDescription course
                    <dd.col-sm-9.offset-sm-3>#{desc}
            $maybe universityid <- muniversityid
                <dt.col-sm-3>University Id
                <dd.col-sm-9>#{universityid}
        $if not isLti
            <button type="button" class="btn btn-primary" data-toggle="modal" data-target="#updateUserData">
                Edit
    |]

updateUserDataForm
    :: UserData
    -> [Entity Course]
    -> B.Markup
    -> MForm (HandlerFor App) (FormResult (Maybe (Entity Course), Text, Text, Maybe Text), WidgetFor App ())
updateUserDataForm UserData {userDataUniversityId = muniversityid, userDataFirstName = firstname, userDataLastName = lastname} classes =
    renderBootstrap3 BootstrapBasicForm $ (,,,)
            <$> aopt (selectFieldList classnames) classfieldSettings Nothing
            <*> areq textField (bfs ("First Name"::Text)) (Just firstname)
            <*> areq textField (bfs ("Last Name"::Text)) (Just lastname)
            <*> aopt textField (bfs ("University Id"::Text)) (Just muniversityid)
    where openClasses = filter (\(Entity _ course) -> courseEnrollmentOpen course) classes
          classnames = map (\theclass -> (courseTitle . entityVal $ theclass, theclass)) openClasses
          classfieldSettings = case classes of 
                                    _:_ -> bfs ("Course Enrollment " :: Text ) 
                                    [] -> FieldSettings 
                                            { fsLabel = ""
                                            , fsTooltip = Nothing
                                            , fsId = Nothing
                                            , fsName = Nothing
                                            , fsAttrs = [("style","display:none")]
                                            }

dropClassForm :: B.Markup -> MForm (HandlerFor App) (FormResult (), WidgetFor App ())
dropClassForm = renderBootstrap3 BootstrapBasicForm $ pure () 

nouserPage :: WidgetFor site ()
nouserPage = [whamlet|
             <div.container>
                <p> This user does not exist
             |]
