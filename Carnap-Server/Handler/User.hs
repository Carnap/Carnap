{-# LANGUAGE LambdaCase #-}
module Handler.User where

import Import
import Control.Monad (fail)
import Text.Read (read, readMaybe)
import qualified Text.Blaze.Html5 as B
import Carnap.GHCJS.SharedTypes
import Yesod.Form.Bootstrap3
import Data.Time
import Data.List ((!!),elemIndex)
import Data.Time.Zones
import Data.Time.Zones.All
import Util.Data
import Util.Database
import qualified Data.IntMap as IM
import Data.IntMap ((!))

postUserR :: Text -> Handler Html
postUserR ident = do
    musr <- runDB $ getBy $ UniqueUser ident
    case musr of
        Nothing -> defaultLayout nouserPage
        (Just (Entity uid _))  -> do
            ud <- checkUserData uid
            time <- liftIO getCurrentTime
            classes <- runDB $ selectList [CourseStartDate <. time, CourseEndDate >. time] []
            ((updateRslt,_),_) <- runFormPost (updateUserDataForm ud classes)
            case updateRslt of
                 (FormFailure s) -> setMessage $ "Something went wrong: " ++ B.toMarkup (show s)
                 FormMissing -> setMessage "Submission data incomplete"
                 (FormSuccess (mc, fn , ln)) -> runDB $ do
                         mudent <- getBy $ UniqueUserData uid
                         case entityKey <$> mudent of
                               Nothing -> return ()
                               Just udid -> do
                                    case mc of
                                        Nothing -> update udid [ UserDataFirstName =. fn
                                                              , UserDataLastName =. ln]
                                        Just c -> update udid [ UserDataFirstName =. fn
                                                              , UserDataLastName =. ln
                                                              , UserDataEnrolledIn =. (Just $ entityKey c)]
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
            ud@UserData {
                  userDataEnrolledIn = maybeCourseId
                , userDataInstructorId = maybeInstructorId
                , userDataFirstName = firstname
                , userDataLastName = lastname
                } <- checkUserData uid
            time <- liftIO getCurrentTime
            classes <- runDB $ selectList [CourseStartDate <. time, CourseEndDate >. time] []
            (updateForm,encTypeUpdate) <- generateFormPost (updateUserDataForm ud classes)
            let isInstructor = case maybeInstructorId of Just _ -> True; _ -> False
            derivedRulesOld <- getDerivedRules uid
            derivedRulesNew <- getRules uid

            maybeCourse <- case maybeCourseId of
                              Just cid -> do runDB $ get cid
                              Nothing  -> return Nothing
            case maybeCourse of
                Just course -> do
                       -- safety: `Nothing` case unreachable since `maybeCourse` will be `Nothing` also
                       let Just cid = maybeCourseId
                       asmd <- runDB $ selectList [AssignmentMetadataCourse ==. cid] []
                       asDocs <- mapM (runDB . get) (map (assignmentMetadataDocument . entityVal) asmd)
                       textbookproblems <- getProblemSets cid
                       extension <- (runDB $ getBy $ UniqueAccommodation cid uid)
                                    >>= return . maybe 0 (accommodationDateExtraHours . entityVal)
                       assignments <- assignmentsOf extension course textbookproblems asmd asDocs
                       pq <- getProblemQuery uid cid
                       let getSubs typ = map entityVal <$> runDB (selectList ([ProblemSubmissionType ==. typ] ++ pq) [])
                       subs <- mapM getSubs [SyntaxCheck,Translation,Derivation,TruthTable,CounterModel,Qualitative,SequentCalc,DeductionTree]
                       mapM (problemsToTable course extension textbookproblems asmd asDocs) subs
                           >>= \case
                              [syntable,transtable,dertable,tttable,cmtable,qtable,seqtable,treetable] -> do
                                   score <- totalScore extension textbookproblems (concat subs)
                                   defaultLayout $ do
                                       addScript $ StaticR js_bootstrap_bundle_min_js
                                       addScript $ StaticR js_bootstrap_min_js
                                       setTitle "Welcome To Your Homepage!"
                                       $(widgetFile "user")
                              _ -> liftIO $ fail "incorrect number of tables: this should never happen"
                Nothing -> defaultLayout $ do
                                addScript $ StaticR js_bootstrap_bundle_min_js
                                addScript $ StaticR js_bootstrap_min_js
                                [whamlet|
                                <div.container>
                                    ^{updateWidget updateForm encTypeUpdate}
                                    <p> This user is not enrolled
                                    $if isInstructor
                                        <p> Your instructor page is #
                                            <a href=@{InstructorR ident}>here

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
--Grading
--------------------------------------------------------
--functions for calculating grades

toScore
    :: Int
    -> Maybe BookAssignmentTable
    -> ProblemSubmission
    -> HandlerFor App Int
toScore extension textbookproblems p = 
        case (problemSubmissionAssignmentId p, problemSubmissionCorrect p) of
               (_,False) -> return extra
               (Nothing,True) -> return $
                    case ( utcDueDate textbookproblems (problemSubmissionIdent p)
                         , problemSubmissionCredit p) of
                          (Just d, Just c) ->  theGrade d c p + extra
                          (Just d, Nothing) ->  theGrade d 5 p + extra
                          (Nothing,_) -> 0
               (Just a,True) -> do
                    mmd <- runDB $ get a
                    case mmd of
                        Nothing -> return 0
                        Just v -> return $
                            case ( assignmentMetadataDuedate v
                                 , problemSubmissionCredit p) of
                                    (Just d, Just c) -> theGrade d c p + extra
                                    (Just d, Nothing) -> theGrade d 5 p + extra
                                    (Nothing, Just c) -> c + extra
                                    (Nothing, Nothing) -> 5 + extra
    where extra = case problemSubmissionExtra p of Nothing -> 0; Just e -> e
          extensionUTC = fromIntegral (3600 * extension) :: NominalDiffTime
          theGrade :: UTCTime -> Int -> ProblemSubmission -> Int
          theGrade due points p' = 
            case problemSubmissionLateCredit p' of
                  Nothing | problemSubmissionTime p' `laterThan` (extensionUTC `addUTCTime` due) -> floor ((fromIntegral points :: Rational) / 2)
                  Just n  | problemSubmissionTime p' `laterThan` (extensionUTC `addUTCTime` due) -> n
                  _ -> points

scoreByIdAndClassTotal :: Key Course -> Key User -> HandlerFor App Int
scoreByIdAndClassTotal cid uid =
        do perprob <- scoreByIdAndClassPerProblem cid uid
           return $ foldr (+) 0 (map snd perprob)

scoreByIdAndClassPerProblem :: Key Course -> Key User -> HandlerFor App [(Either (Key AssignmentMetadata) Text, Int)]
scoreByIdAndClassPerProblem cid uid =
        do pq <- getProblemQuery uid cid
           subs <- map entityVal <$> (runDB $ selectList pq [])
           textbookproblems <- getProblemSets cid
           extension <- (runDB $ getBy $ UniqueAccommodation cid uid) 
                        >>= return . maybe 0 (accommodationDateExtraHours . entityVal)
           scoreList extension textbookproblems subs

totalScore :: (Traversable t, MonoFoldable (t Int), Num (Element (t Int))) => 
    Int -> Maybe BookAssignmentTable -> t ProblemSubmission -> HandlerFor App (Element (t Int))
totalScore extension textbookproblems xs =
        do xs' <- mapM (toScore extension textbookproblems) xs
           return $ foldr (+) 0 xs'

scoreList :: Traversable t => Int -> Maybe BookAssignmentTable -> t ProblemSubmission 
    -> HandlerFor App (t (Either (Key AssignmentMetadata) Text, Int))
scoreList extension textbookproblems = mapM (\x -> do score <- toScore extension textbookproblems x
                                                      return (getLabel x, score))
   where getLabel x = case problemSubmissionAssignmentId x of
                          --get assignment metadata id
                          Just amid -> Left amid
                          --otherwise, must be a textbook problem
                          Nothing -> Right $ takeWhile (/= '.') (problemSubmissionIdent x)

--------------------------------------------------------
--Due dates
--------------------------------------------------------
--functions for dealing with time and due dates

dateDisplay :: UTCTime -> Course -> String
dateDisplay inUtc course = case tzByName $ courseTimeZone course of
                             Just tz  -> formatTime defaultTimeLocale "%F %R %Z" $ utcToZonedTime (timeZoneForUTCTime tz inUtc) inUtc
                             Nothing -> formatTime defaultTimeLocale "%F %R UTC" $ utc

utcDueDate :: (IsSequence t, Element t ~ Char) => Maybe BookAssignmentTable -> t -> Maybe UTCTime
utcDueDate textbookproblems x = textbookproblems >>= IM.lookup theIndex . readAssignmentTable
    where theIndex = read . unpack . takeWhile (/= '.') $ x :: Int

--------------------------------------------------------
--Components
--------------------------------------------------------
--reusable components
problemsToTable :: Course -> Int -> Maybe BookAssignmentTable 
    -> [Entity AssignmentMetadata] -> [Maybe Document] -> [ProblemSubmission] 
    -> HandlerFor App Html
problemsToTable course extension textbookproblems asmd asDocs submissions = do
            rows <- mapM toRow submissions
            withUrlRenderer [hamlet|
                                    $forall row <- rows
                                        ^{row}|]
        where toRow p = do score <- toScore extension textbookproblems p
                           return [hamlet|
                                  <tr>
                                    <td>^{printSource (problemSubmissionSource p)}
                                    <td>#{problemSubmissionIdent p}
                                    <td title="#{displayProblemData $ problemSubmissionData p}">
                                        <div.problem-display> #{displayProblemData $ problemSubmissionData p}
                                    <td>#{dateDisplay (problemSubmissionTime p) course}
                                    <td>#{show $ score}
                                    <td>#{show $ problemSubmissionType p}|]

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

--properly localized assignments for a given class
--XXX---should this just be in the hamlet?
assignmentsOf :: Int -> Course -> Maybe BookAssignmentTable -> [Entity AssignmentMetadata] -> [Maybe Document] -> HandlerFor App (WidgetFor App ())
assignmentsOf extension course textbookproblems asmd asDocs = do
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
                                $forall (num,date) <- IM.toList (readAssignmentTable dd)
                                    <tr>
                                        <td>
                                            <a href=@{ChapterR $ chapterOfProblemSet ! num}>
                                                Problem Set #{show num}
                                        <td>
                                            #{dateDisplay (addUTCTime extensionUTC date) course}
                                        <td>
                            $forall (Entity _ a, Just d) <- zip asmd asDocs
                                $if visibleAt time a
                                        <tr>
                                            <td>
                                                <a href=@{CourseAssignmentR (courseTitle course) (documentFilename d)}>
                                                    #{documentFilename d}
                                            $maybe due <- assignmentMetadataDuedate a
                                                <td>#{dateDisplay due course}
                                            $nothing
                                                <td>No Due Date
                                            $maybe desc <- assignmentMetadataDescription a
                                                <td>
                                                    <div.assignment-desc>#{desc}
                                            $nothing
                                                <td>-
                |]
    where extensionUTC = fromIntegral (3600 * extension) :: NominalDiffTime
          visibleAt t a = case assignmentMetadataAvailability a of
                              Just status | availabilityHidden status -> False
                              _ -> (assignmentMetadataVisibleTill a > Just t || assignmentMetadataVisibleTill a == Nothing)
                                   && (assignmentMetadataVisibleFrom a < Just t || assignmentMetadataVisibleFrom a == Nothing)

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

personalInfo :: UserData -> Maybe Course -> WidgetFor site ()
personalInfo (UserData {userDataFirstName = firstname, userDataLastName = lastname}) mcourse =
        [whamlet| <div.card>
                        <div.card-header> Personal Information
                        <div.card-block>
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
                            <button type="button" class="btn btn-primary" data-toggle="modal" data-target="#updateUserData">
                                Edit
                            |]

updateUserDataForm
    :: UserData
    -> [Entity Course]
    -> B.Markup
    -> MForm (HandlerFor App) (FormResult (Maybe (Entity Course), Text, Text), WidgetFor App ())
updateUserDataForm UserData {userDataFirstName=firstname, userDataLastName=lastname} classes =
    renderBootstrap3 BootstrapBasicForm $ (,,)
            <$> aopt (selectFieldList classnames) (bfs ("Class" :: Text)) Nothing
            <*> areq textField (bfs ("First Name"::Text)) (Just firstname)
            <*> areq textField (bfs ("Last Name"::Text)) (Just lastname)
    where classnames = map (\theclass -> (courseTitle . entityVal $ theclass, theclass)) classes

nouserPage :: WidgetFor site ()
nouserPage = [whamlet|
             <div.container>
                <p> This user does not exist
             |]
