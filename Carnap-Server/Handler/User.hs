module Handler.User where

import Import
import Text.Read (read, readMaybe)
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.GHCJS.SharedTypes
import Yesod.Form.Bootstrap3
import Data.Time
import Data.List ((!!),elemIndex)
import Data.Time.Zones
import Data.Time.Zones.All
import Data.Aeson (decodeStrict)
import Util.Data
import Util.Database
import qualified Data.Map as M
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
deleteUserR ident = do
    msg <- requireJsonBody :: Handler Text
    maybeCurrentUserId <- maybeAuthId
    case maybeCurrentUserId of
        Nothing -> return ()
        Just u -> runDB $ do kl <- selectKeysList [SavedDerivedRuleUserId ==. u
                                                  ,SavedDerivedRuleName ==. msg ] []
                             case kl of
                                 [] -> return ()
                                 (targetkey:_) -> delete targetkey
    returnJson (msg ++ " deleted")

getUserR :: Text -> Handler Html
getUserR ident = do
    musr <- runDB $ getBy $ UniqueUser ident
    case musr of 
        Nothing -> defaultLayout nouserPage
        (Just (Entity uid _))  -> do
            ud@(UserData firstname lastname maybeCourseId maybeInstructorId _) <- checkUserData uid
            time <- liftIO getCurrentTime
            classes <- runDB $ selectList [CourseStartDate <. time, CourseEndDate >. time] []
            (updateForm,encTypeUpdate) <- generateFormPost (updateUserDataForm ud classes)
            let isInstructor = case maybeInstructorId of Just _ -> True; _ -> False
            derivedRules <- getDerivedRules uid
            case maybeCourseId of
                Just cid ->
                    do Just course <- runDB $ get cid
                       asmd <- runDB $ selectList [AssignmentMetadataCourse ==. cid] []
                       asDocs <- mapM (runDB . get) (map (assignmentMetadataDocument . entityVal) asmd)
                       textbookproblems <- getProblemSets cid
                       assignments <- assignmentsOf course textbookproblems asmd asDocs
                       pq <- getProblemQuery uid cid
                       let getSubs typ = map entityVal <$> runDB (selectList ([ProblemSubmissionType ==. typ] ++ pq) [])
                       subs@[synsubs,transsubs,dersubs,ttsubs] <- mapM getSubs [SyntaxCheck,Translation,Derivation,TruthTable]
                       [syntable,transtable,dertable,tttable] <- mapM (problemsToTable course textbookproblems asmd asDocs) subs
                       score <- totalScore textbookproblems (concat subs)
                       defaultLayout $ do
                           addScript $ StaticR js_bootstrap_bundle_min_js
                           addScript $ StaticR js_bootstrap_min_js
                           setTitle "Welcome To Your Homepage!"
                           $(widgetFile "user")
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
    where tryLookup l x = case lookup x l of
                          Just n -> show n
                          Nothing -> "can't find scores"

--------------------------------------------------------
--Grading
--------------------------------------------------------
--functions for calculating grades

toScore textbookproblems p = case ( problemSubmissionAssignmentId p
                                  , problemSubmissionCorrect p
                                  ) of
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
          theGrade :: UTCTime -> Int -> ProblemSubmission -> Int
          theGrade due points p = if problemSubmissionTime p `laterThan` due 
                                      then (floor ((fromIntegral points :: Rational) / 2))
                                      else points
                            
scoreByIdAndClassTotal cid uid = 
        do perprob <- scoreByIdAndClassPerProblem cid uid
           return $ foldr (+) 0 (map snd perprob)

scoreByIdAndClassPerProblem cid uid = 
        do (Just course) <- runDB (get cid)
           textbookproblems <- getProblemSets cid
           pq <- getProblemQuery uid cid
           subs <- map entityVal <$> (runDB $ selectList pq [])
           textbookproblems <-  getProblemSets cid
           scoreList textbookproblems subs

totalScore textbookproblems xs = 
        do xs' <- mapM (toScore textbookproblems) xs
           return $ foldr (+) 0 xs'

scoreList textbookproblems = mapM (\x -> do score <- toScore textbookproblems x
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

dateDisplay utc course = case tzByName $ courseTimeZone course of
                             Just tz  -> formatTime defaultTimeLocale "%F %R %Z" $ utcToZonedTime (timeZoneForUTCTime tz utc) utc
                             Nothing -> formatTime defaultTimeLocale "%F %R UTC" $ utc

utcDueDate textbookproblems x = textbookproblems >>= IM.lookup theIndex . readAssignmentTable
    where theIndex = read . unpack . takeWhile (/= '.') $ x :: Int

laterThan :: UTCTime -> UTCTime -> Bool
laterThan t1 t2 = diffUTCTime t1 t2 > 0

--------------------------------------------------------
--Components 
--------------------------------------------------------
--reusable components

problemsToTable course textbookproblems asmd asDocs submissions = do 
            rows <- mapM toRow submissions
            return $ do B.div B.! class_ "table-responsive" $ do
                            B.table B.! class_ "table table-striped" $ do
                                B.col B.! style "width:100px"
                                B.col B.! style "width:50px"
                                B.col B.! style "width:100px"
                                B.col B.! style "width:100px"
                                B.col B.! style "width:100px"
                                B.thead $ do
                                    B.th "Source"
                                    B.th "Exercise"
                                    B.th "Content"
                                    B.th "Submitted"
                                    B.th "Points Earned"
                                B.tbody $ sequence_ rows
        where toRow p = do score <- toScore textbookproblems p 
                           return $ do
                              B.tr $ do B.td $ printSource (problemSubmissionSource p)
                                        B.td $ B.toHtml (problemSubmissionIdent p)
                                        B.td $ B.toHtml (displayProblemData $ problemSubmissionData p)
                                        B.td $ B.toHtml (dateDisplay (problemSubmissionTime p) course)
                                        B.td $ B.toHtml $ show $ score
              printSource Book = "Textbook"
              printSource (Assignment s) = 
                case (readMaybe s) of
                    Nothing -> "Unknown"
                    Just k -> case elemIndex k (map entityKey asmd) of
                        Nothing -> "No existing assignment"
                        Just n -> case asDocs !! n of
                            Nothing -> "No document"
                            Just d -> B.toHtml $ documentFilename d

tryDelete name = "tryDeleteRule(\"" <> name <> "\")"

--properly localized assignments for a given class 
--XXX---should this just be in the hamlet?
assignmentsOf course textbookproblems asmd asDocs = do
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
                                            #{dateDisplay date course}
                                        <td>-
                            $forall (Entity k a, Just d) <- zip asmd asDocs
                                $if visibleAt time a
                                        <tr>
                                            <td>
                                                <a href=@{AssignmentR $ documentFilename d}>
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
    where visibleAt t a = (assignmentMetadataVisibleTill a > Just t || assignmentMetadataVisibleTill a == Nothing)
                          && (assignmentMetadataVisibleFrom a < Just t || assignmentMetadataVisibleFrom a == Nothing)

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

personalInfo (UserData firstname lastname maybeCourseId maybeInstructorId _) mcourse =
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

updateUserDataForm (UserData firstname lastname maybeCourseId _ _) classes = renderBootstrap3 BootstrapBasicForm $ (,,)
            <$> aopt (selectFieldList classnames) (bfs ("Class" :: Text)) Nothing
            <*> areq textField (bfs ("First Name"::Text)) (Just firstname)
            <*> areq textField (bfs ("Last Name"::Text)) (Just lastname)
    where classnames = map (\theclass -> (courseTitle . entityVal $ theclass, theclass)) classes

nouserPage = [whamlet|
             <div.container>
                <p> This user does not exist
             |]
