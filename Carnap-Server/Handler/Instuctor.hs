{-#LANGUAGE DeriveGeneric #-}
module Handler.Instuctor where

import Import
import Util.Data
import Util.Database
import Yesod.Form.Bootstrap3
import Yesod.Form.Jquery
import Handler.User (scoreByIdAndClassPerProblem)
import Text.Blaze.Html (toMarkup)
import Data.Time
import Data.Time.Zones
import Data.Time.Zones.DB
import Data.Time.Zones.All
import Data.Aeson (decode,encode)
import qualified Data.IntMap (insert,fromList,toList,delete)
import qualified Data.Text as T
import qualified Data.List as L
import System.FilePath
import System.Directory (getDirectoryContents,removeFile, doesFileExist)

putInstructorR :: Text -> Handler Value
putInstructorR ident = do
        ((assignmentrslt,_),_) <- runFormPost (identifyForm "updateAssignment" $ updateAssignmentForm)
        ((courserslt,_),_) <- runFormPost (identifyForm "updateCourse" $ updateCourseForm)
        case (assignmentrslt,courserslt) of 
            (FormSuccess (filename,mdue,mduetime,mdesc),_) -> do
                             massignEnt <- runDB $ getBy $ UniqueAssignment filename
                             case massignEnt of 
                                   Nothing -> return ()
                                   Just (Entity k v) -> 
                                        do let cid = assignmentMetadataCourse v
                                           runDB $ do 
                                                      maybeDo mdue (\due -> 
                                                         do (Just course) <- get cid
                                                            let (Just tz) = tzByName . courseTimeZone $ course
                                                                localdue = case mduetime of
                                                                    (Just time) -> LocalTime due time
                                                                    _ -> LocalTime due (TimeOfDay 23 59 59)
                                                            update k [ AssignmentMetadataDuedate =. (Just $ localTimeToUTCTZ tz localdue) ])
                                                      maybeDo mdesc (\desc -> update k
                                                         [ AssignmentMetadataDescription =. (Just $ unTextarea desc) ])
                             case mdue of Nothing -> returnJson ([filename,"No Due Date"])
                                          Just due -> returnJson ([filename, pack $ show due])
            (_,FormSuccess (coursetitle,mdesc,mstart,mend,mpoints)) -> do
                             Just instructor <- instructorIdByIdent ident
                             mcourseEnt <- runDB . getBy . UniqueCourse coursetitle $ instructor
                             case entityKey <$> mcourseEnt of
                                 Just k -> do runDB $ do maybeDo mdesc (\desc -> update k
                                                           [ CourseDescription =. (Just $ unTextarea desc) ])
                                                         maybeDo mstart (\start -> update k
                                                           [ CourseStartDate =. UTCTime start 0 ])
                                                         maybeDo mend (\end-> update k
                                                           [ CourseEndDate =. UTCTime end 0 ])
                                                         maybeDo mpoints (\points-> update k
                                                           [ CourseTotalPoints =. points ])
                                              returnJson ("updated!"::Text)
                                 Nothing -> returnJson ("could not find course!"::Text)

            (FormFailure s,FormFailure s') -> returnJson ("errors: " <> concat s <> ", " <> concat s' :: Text)
            (_,FormFailure s) -> returnJson ("error on course edit: " <> concat s :: Text)
            (FormFailure s,_) -> returnJson ("error on assignment edit: " <> concat s :: Text)
            (FormMissing,FormMissing) -> returnJson ("no form" :: Text)
    where maybeDo mv f = case mv of Just v -> f v; _ -> return ()

deleteInstructorR :: Text -> Handler Value
deleteInstructorR ident = do
    msg <- requireJsonBody :: Handler InstructorDelete
    case msg of 
      DeleteAssignment fn ->
        do datadir <- appDataRoot <$> (appSettings <$> getYesod) 
           deleted <- runDB $ do mk <- getBy $ UniqueAssignment fn
                                 case mk of
                                     Just (Entity k v) -> 
                                        do deleteCascade k
                                           liftIO $ do fe <- doesFileExist (datadir </> "assignments" </> unpack fn) 
                                                       if fe then removeFile (datadir </> "assignments" </> unpack fn)
                                                             else return ()
                                           return True
                                     Nothing -> return False
           if deleted 
               then returnJson (fn ++ " deleted")
               else returnJson ("unable to retrieve metadata for " ++ fn)
      DeleteProblems coursename setnum -> 
        do miid <- instructorIdByIdent ident
           case miid of
               Just iid -> 
                    do mclass <- runDB $ getBy $ UniqueCourse coursename iid
                       case mclass of 
                            Just (Entity classkey theclass)->
                                do case readAssignmentTable <$> courseTextbookProblems theclass  of
                                       Just assign -> do runDB $ update classkey
                                                                        [CourseTextbookProblems =. (Just $ BookAssignmentTable $ Data.IntMap.delete setnum assign)]
                                                         returnJson ("Deleted Assignment"::Text)
                                       Nothing -> returnJson ("Assignment table Missing, can't delete."::Text)
                            Nothing -> returnJson ("Something went wrong with retriving the course."::Text)

               Nothing -> returnJson ("You do not appear to be an instructor."::Text)
      DeleteCourse coursename -> 
        do miid <- instructorIdByIdent ident
           case miid of
               Just iid -> 
                    do mclass <- runDB $ getBy $ UniqueCourse coursename iid
                       case mclass of 
                            Just (Entity classkey theclass)-> 
                                do runDB $ do studentsOf <- selectList [UserDataEnrolledIn ==. Just classkey] []
                                              mapM (\s -> update (entityKey s) [UserDataEnrolledIn =. Nothing]) studentsOf
                                              deleteCascade classkey
                                   returnJson ("Class Deleted"::Text)
                            Nothing -> returnJson ("No class to delete, for some reason"::Text)

postInstructorR :: Text -> Handler Html
postInstructorR ident = do
    classes <- classesByInstructorIdent ident
    ((assignmentrslt,_),_) <- runFormPost (identifyForm "uploadAssignment" $ uploadAssignmentForm classes)
    ((newclassrslt,_),_) <- runFormPost (identifyForm "createCourse" createCourseForm)
    ((frombookrslt,_),_) <- runFormPost (identifyForm "setBookAssignment" $ setBookAssignmentForm classes)
    case assignmentrslt of 
        (FormSuccess (file, Entity classkey theclass, duedate,duetime, assignmentdesc, subtime)) ->
            do let fn = fileName file
                   (Just tz) = tzByName . courseTimeZone $ theclass
                   localdue = case (duedate,duetime) of
                                  (Just date, Just time) -> Just $ LocalTime date time
                                  (Just date,_)  -> Just $ LocalTime date (TimeOfDay 23 59 59)
                                  _ -> Nothing
                   info = unTextarea <$> assignmentdesc
               success <- tryInsert $ AssignmentMetadata fn info (localTimeToUTCTZ tz <$> localdue) subtime classkey 
               if success then saveAssignment file 
                          else setMessage "A file with this name already exists in Carnap's database. Perhaps you could make the name unique by adding your name or course title?"
        (FormFailure s) -> setMessage $ "Something went wrong: " ++ toMarkup (show s)
        FormMissing -> return ()
    case newclassrslt of
        (FormSuccess (title, coursedesc, startdate, enddate, tzlabel)) -> do
            miid <- instructorIdByIdent ident
            case miid of
                Just iid -> 
                    do let localize x = localTimeToUTCTZ (tzByLabel tzlabel) (LocalTime x midnight)
                       success <- tryInsert $ Course title (unTextarea <$> coursedesc) iid Nothing (localize startdate) (localize enddate) 0 (toTZName tzlabel)
                       if success then setMessage "Course Created" 
                                  else setMessage "Could not save---this course already exists"
                Nothing -> setMessage "you're not an instructor!"
        (FormFailure s) -> setMessage $ "Something went wrong: " ++ toMarkup (show s)
        FormMissing -> return ()
    case frombookrslt of
        (FormSuccess (Entity classkey theclass, theassignment, duedate, mduetime)) -> runDB $ do
            let (Just tz) = tzByName . courseTimeZone $ theclass
                localdue = case mduetime of
                              Just time -> LocalTime duedate time
                              _ -> LocalTime duedate (TimeOfDay 23 59 59)
                due = localTimeToUTCTZ tz localdue
            case readAssignmentTable <$> courseTextbookProblems theclass of
                Just assign -> update classkey [CourseTextbookProblems =. (Just $ BookAssignmentTable $ Data.IntMap.insert theassignment due assign)]
                Nothing -> update classkey [CourseTextbookProblems =. (Just $ BookAssignmentTable $ Data.IntMap.fromList [(theassignment, due)])]
        (FormFailure s) -> setMessage $ "Something went wrong: " ++ toMarkup (show s)
        FormMissing -> return ()
    redirect $ InstructorR ident

getInstructorR :: Text -> Handler Html
getInstructorR ident = do
    musr <- runDB $ getBy $ UniqueUser ident
    case musr of 
        Nothing -> defaultLayout nopage
        (Just (Entity uid _))  -> do
            UserData firstname lastname enrolledin _ _ <- checkUserData uid 
            classes <- classesByInstructorIdent ident 
            let tags = map tagOf classes
            classWidgets <- mapM classWidget classes
            instructorCourses <- classesByInstructorIdent ident
            assignmentMetadata <- concat <$> mapM (assignmentsOf . entityKey) classes
            assignmentCourses <- forM assignmentMetadata $ \c -> do 
                                    Just e <- runDB $ get (assignmentMetadataCourse c)
                                    return e
            (uploadAssignmentWidget,enctypeUploadAssignment) <- generateFormPost (identifyForm "uploadAssignment" $ uploadAssignmentForm classes)
            (setBookAssignmentWidget,enctypeSetBookAssignment) <- generateFormPost (identifyForm "setBookAssignment" $ setBookAssignmentForm classes)
            (updateAssignmentWidget,enctypeUpdateAssignment) <- generateFormPost (identifyForm "updateAssignment" $ updateAssignmentForm)
            (createCourseWidget,enctypeCreateCourse) <- generateFormPost (identifyForm "createCourse" createCourseForm)
            (updateCourseWidget,enctypeUpdateCourse) <- generateFormPost (identifyForm "updateCourse" $ updateCourseForm)
            defaultLayout $ do
                 addScript $ StaticR js_bootstrap_bundle_min_js
                 addScript $ StaticR js_bootstrap_min_js
                 setTitle $ "Instructor Page for " ++ toMarkup firstname ++ " " ++ toMarkup lastname
                 $(widgetFile "instructor")
    where assignmentsOf theclass = map entityVal <$> listAssignmentMetadata theclass
          tagOf = T.append "course-" . T.map (\c -> if c `elem` [' ',':'] then '_' else c) . courseTitle . entityVal
          mprobsOf course = readAssignmentTable <$> courseTextbookProblems course
          nopage = [whamlet|
                    <div.container>
                        <p> Instructor not found.
                   |]

---------------------
--  Message Types  --
---------------------

data InstructorDelete = DeleteAssignment Text
                      | DeleteProblems Text Int
                      | DeleteCourse Text
    deriving Generic

instance ToJSON InstructorDelete

instance FromJSON InstructorDelete

------------------
--  Components  --
------------------

uploadAssignmentForm classes = renderBootstrap3 BootstrapBasicForm $ (,,,,,)
            <$> fileAFormReq (bfs ("Assignment" :: Text))
            <*> areq (selectFieldList classnames) (bfs ("Class" :: Text)) Nothing
            <*> aopt (jqueryDayField def) (bfs ("Due Date"::Text)) Nothing
            <*> aopt timeFieldTypeTime (bfs ("Due Time"::Text)) Nothing
            <*> aopt textareaField (bfs ("Assignment Description"::Text)) Nothing
            <*> lift (liftIO getCurrentTime)
    where classnames = map (\theclass -> (courseTitle . entityVal $ theclass, theclass)) classes

updateAssignmentModal form enc = [whamlet|
                    <div class="modal fade" id="updateAssignmentData" tabindex="-1" role="dialog" aria-labelledby="updateAssignmentDataLabel" aria-hidden="true">
                        <div class="modal-dialog" role="document">
                            <div class="modal-content">
                                <div class="modal-header">
                                    <h5 class="modal-title" id="updateAssignmentDataLabel">Update Assignment Data</h5>
                                    <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                      <span aria-hidden="true">&times;</span>
                                <div class="modal-body">
                                    <form#updateAssignment enctype=#{enc}>
                                        ^{form}
                                        <div.form-group>
                                            <input.btn.btn-primary type=submit value="update">
                    |]    

updateAssignmentForm = renderBootstrap3 BootstrapBasicForm $ (,,,)
            <$> areq fileName "" Nothing
            <*> aopt (jqueryDayField def) (bfs ("Due Date"::Text)) Nothing
            <*> aopt timeFieldTypeTime (bfs ("Due Time"::Text)) Nothing
            <*> aopt textareaField (bfs ("Assignment Description"::Text)) Nothing
    where fileName :: (Monad m, RenderMessage (HandlerSite m) FormMessage) => Field m Text 
          fileName = hiddenField

setBookAssignmentForm classes = renderBootstrap3 BootstrapBasicForm $ (,,,)
            <$> areq (selectFieldList classnames) (bfs ("Class" :: Text)) Nothing
            <*> areq (selectFieldList chapters) (bfs ("Problem Set" :: Text))  Nothing
            <*> areq (jqueryDayField def) (bfs ("Due Date"::Text)) Nothing
            <*> aopt timeFieldTypeTime (bfs ("Due Time"::Text)) Nothing
    where chapters = map (\x -> ("Problem Set " ++ pack (show x),x)) [1..17] :: [(Text,Int)]
          classnames = map (\theclass -> (courseTitle . entityVal $ theclass, theclass)) classes

createCourseForm = renderBootstrap3 BootstrapBasicForm $ (,,,,)
            <$> areq textField (bfs ("Title" :: Text)) Nothing
            <*> aopt textareaField (bfs ("Course Description"::Text)) Nothing
            <*> areq (jqueryDayField def) (bfs ("Start Date"::Text)) Nothing
            <*> areq (jqueryDayField def) (bfs ("End Date"::Text)) Nothing
            <*> areq (selectFieldList zones)    (bfs ("TimeZone"::Text)) Nothing
    where zones = map (\(x,y,_) -> (decodeUtf8 x,y)) (rights tzDescriptions)

updateCourseModal form enc = [whamlet|
                    <div class="modal fade" id="updateCourseData" tabindex="-1" role="dialog" aria-labelledby="updateCourseDataLabel" aria-hidden="true">
                        <div class="modal-dialog" role="document">
                            <div class="modal-content">
                                <div class="modal-header">
                                    <h5 class="modal-title" id="updateCourseDataLabel">Update Course Data</h5>
                                    <button type="button" class="close" data-dismiss="modal" aria-label="Close">
                                      <span aria-hidden="true">&times;</span>
                                <div class="modal-body">
                                    <form#updateCourse enctype=#{enc}>
                                        ^{form}
                                        <div.form-group>
                                            <input.btn.btn-primary type=submit value="update">
                    |]

updateCourseForm = renderBootstrap3 BootstrapBasicForm $ (,,,,)
            <$> areq courseName "" Nothing
            <*> aopt textareaField (bfs ("Course Description"::Text)) Nothing
            <*> aopt (jqueryDayField def) (bfs ("Start Date"::Text)) Nothing
            <*> aopt (jqueryDayField def) (bfs ("End Date"::Text)) Nothing
            <*> aopt intField (bfs ("Total Points for Course"::Text)) Nothing
    where courseName :: (Monad m, RenderMessage (HandlerSite m) FormMessage) => Field m Text 
          courseName = hiddenField

saveAssignment file = do
        let assignmentname = unpack $ fileName file
        datadir <- appDataRoot <$> (appSettings <$> getYesod)
        let path = datadir </> "assignments" </> assignmentname
        liftIO $ fileMove file path

classWidget :: Entity Course -> HandlerT App IO Widget
classWidget classent = do
       let cid = entityKey classent
           course = entityVal classent
           mprobs = readAssignmentTable <$> courseTextbookProblems course :: Maybe (IntMap UTCTime)
       allUserData <- map entityVal <$> (runDB $ selectList [UserDataEnrolledIn ==. Just cid] [])
       asmd <- runDB $ selectList [AssignmentMetadataCourse ==. cid] []
       let allUids = (map userDataUserId  allUserData)
       musers <- mapM (\x -> runDB (get x)) allUids
       let users = catMaybes musers
       allScores <- zip (map userIdent users) <$> mapM (scoreByIdAndClassPerProblem cid) allUids 
       let usersAndData = zip users allUserData
       (Just course) <- runDB $ get cid
       return [whamlet|
                    <h2>Assignments
                    <table.table.table-striped>
                        <thead>
                            <th> Assignment
                            <th> Due Date
                            <th> Submissions
                            <th> High Score
                            <th> Low Score
                            <th> Submission Average
                        <tbody>
                            $maybe probs <- mprobs
                                $forall (set,due) <- Data.IntMap.toList probs
                                    <tr>
                                        <td>Problem Set #{show set}
                                        <td>#{dateDisplay due course}
                                        ^{analyticsFor (Right (pack (show set))) allScores}
                        $forall Entity k a <- asmd
                            <tr>
                                <td>
                                    <a href=@{AssignmentR $ assignmentMetadataFilename a}>
                                        #{assignmentMetadataFilename a}
                                $maybe due <- assignmentMetadataDuedate a
                                    <td>#{dateDisplay due course}
                                $nothing
                                    <td>No Due Date
                                ^{analyticsFor (Left k) allScores}
                    <h2>Students
                    <table.table.table-striped>
                        <thead>
                            <th> Registered Student
                            <th> Student Name
                            <th> Total Score
                        <tbody>
                            $forall (u,UserData fn ln _ _ _) <- usersAndData
                                <tr>
                                    <td>
                                        <a href=@{UserR (userIdent u)}>#{userIdent u}
                                    <td>
                                        #{ln}, #{fn}
                                    <td>
                                        #{totalByUser (userIdent u) allScores}/#{show $ courseTotalPoints course}
                    <h2>Course Data
                    <dl.row>
                        <dt.col-sm-3>Course Title
                        <dd.col-sm-9>#{courseTitle course}
                        $maybe desc <- courseDescription course
                            <dd.col-sm-9.offset-sm-3>#{desc}
                        <dt.col-sm-3>Points Available
                        <dd.col-sm-9>#{courseTotalPoints course}
                        <dt.col-sm-3>Start Date
                        <dd.col-sm-9>#{dateDisplay (courseStartDate course) course}
                        <dt.col-sm-3>End Date
                        <dd.col-sm-9>#{dateDisplay (courseEndDate course) course}
                        <dt.col-sm-3>Time Zone
                        <dd.col-sm-9>#{decodeUtf8 $ courseTimeZone course}
                    <button.btn.btn-sm.btn-danger type="button" onclick="tryDeleteCourse('#{decodeUtf8 $ encode $ DeleteCourse (courseTitle course)}')">
                        Delete Course
                    <button.btn.btn-sm.btn-secondary type="button"  onclick="modalEditCourse('#{courseTitle course}')">
                        Edit Course Information
              |]
    where totalByUser uident scores = case lookup uident scores of
                                Just xs -> show $ foldr (+) 0 (map snd xs)
                                Nothing -> "can't find scores"
          analyticsFor assignment scores = 
                do --list the per-problem scores of each user for this assignment
                   let thescores = map (\(x,y) -> map snd $ filter (\x -> fst x == assignment) y) scores
                       --extract data
                       submissions = filter (/= []) thescores
                       thereareany = length submissions > 0
                       totals = map sum submissions
                       highscore = if thereareany then show (L.maximum totals) else "N/A"
                       lowscore = if thereareany then show (L.minimum totals) else "N/A"
                       average = if thereareany then  show $ sum totals `div` length submissions else "N/A"
                   [whamlet|
                          <td>
                              #{length submissions}/#{length thescores}
                          <td>
                              #{highscore}
                          <td>
                              #{lowscore}
                          <td>
                              #{average}
                          |]


dateDisplay utc course = case tzByName $ courseTimeZone course of
                             Just tz  -> show $ utcToZonedTime (timeZoneForUTCTime tz utc) utc
                             Nothing -> show $ utc

-- TODO compare directory contents with database results
listAssignmentMetadata theclass = do asmd <- runDB $ selectList [AssignmentMetadataCourse ==. theclass] []
                                     return asmd
