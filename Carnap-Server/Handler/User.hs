module Handler.User where

import Import
import Prelude (read)
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.GHCJS.SharedTypes
import Yesod.Form.Bootstrap3
import Data.Time
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
            classes <- runDB $ selectList [] []
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
        (Just (Entity k _))  -> do
            ud@(UserData firstname lastname maybeCourseId maybeInstructorId _) <- checkUserData k
            classes <- runDB $ selectList [] []
            (updateForm,encTypeUpdate) <- generateFormPost (updateUserDataForm ud classes)
            (synsubs, transsubs,dersubs, ttsubs) <- subsByIdAndSource maybeCourseId k
            let isInstructor = case maybeInstructorId of Just _ -> True; _ -> False
            derivedRules <- getDerivedRules k
            case maybeCourseId of
                Just cid ->
                    do Just course <- runDB $ get cid
                       textbookproblems <- getProblemSets cid
                       assignments <- assignmentsOf cid textbookproblems
                       syntable <- problemsToTable course textbookproblems synsubs
                       transtable <- problemsToTable course textbookproblems transsubs
                       dertable <- problemsToTable course textbookproblems dersubs
                       tttable <- problemsToTable course textbookproblems ttsubs
                       score <- totalScore textbookproblems synsubs transsubs dersubs ttsubs
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
                                        <p> Your instructor page is 
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

toScore textbookproblems p = case assignment p of
                   Nothing -> 
                        case utcDueDate textbookproblems (problem p) of                      
                              Just d -> if submitted p `laterThan` d       
                                            then return (2 :: Int)
                                            else return (5 :: Int)
                              Nothing -> return (0 :: Int)
                   Just a -> do
                        mmd <- runDB $ get a
                        case mmd of
                            Nothing -> return (0 :: Int)
                            Just v -> case assignmentMetadataDuedate v of 
                                        Just due | submitted p `laterThan` due -> return (2 :: Int)
                                        _ -> return (5 :: Int)
                            
scoreByIdAndClassTotal cid uid = 
        do perprob <- scoreByIdAndClassPerProblem cid uid
           return $ foldr (+) 0 (map snd perprob)

scoreByIdAndClassPerProblem cid uid = 
        do (a,b,c,d) <- subsByIdAndSource (Just cid) uid
           textbookproblems <-  getProblemSets cid
           scoreList textbookproblems a b c d

totalScore textbookproblems a b c d = do
           (a',b',c',d') <- (,,,) <$> score a <*> score b <*> score c <*> score d
           return $ a' + b' + c' + d'
   where score :: Problem p => [p] -> Handler Int
         score xs = do xs' <- mapM (toScore textbookproblems) xs
                       return $ foldr (+) 0 xs'

scoreList textbookproblems a b c d = 
        do (a',b',c',d') <- (,,,) <$> toScoreList a <*> toScoreList b <*> toScoreList c <*> toScoreList d
           return $ concat [a',b',c',d']
   where toScoreList :: Problem p => [p] -> Handler [(Either AssignmentMetadataId Text, Int)]
         toScoreList xs = mapM (\x -> do score <- toScore textbookproblems x
                                         return (getLabel x, score)) xs
         
         getLabel x = case assignment x of
                          --get assignment metadata id
                          Just amid -> Left amid
                          --otherwise, must be a textbook problem
                          Nothing -> Right $ takeWhile (/= '.') (problem x) 

--------------------------------------------------------
--Due dates
--------------------------------------------------------
--functions for dealing with time and due dates

dateDisplay utc course = case tzByName $ courseTimeZone course of
                             Just tz  -> show $ utcToZonedTime (timeZoneForUTCTime tz utc) utc
                             Nothing -> show $ utc

utcDueDate textbookproblems x = textbookproblems >>= IM.lookup theIndex . readAssignmentTable
    where theIndex = read . unpack . takeWhile (/= '.') $ x :: Int

laterThan :: UTCTime -> UTCTime -> Bool
laterThan t1 t2 = diffUTCTime t1 t2 > 0

--------------------------------------------------------
--Components 
--------------------------------------------------------
--reusable components

problemsToTable course textbookproblems xs = do 
            rows <- mapM toRow xs
            return $ do B.table B.! class_ "table table-striped" $ do
                            B.col B.! style "width:50px"
                            B.col B.! style "width:100px"
                            B.col B.! style "width:100px"
                            B.col B.! style "width:100px"
                            B.thead $ do
                                B.th "Exercise"
                                B.th "Content"
                                B.th "Submitted"
                                B.th "Points Earned"
                            B.tbody $ sequence_ rows
        where toRow p = do score <- toScore textbookproblems p 
                           return $ do
                              B.tr $ do B.td $ B.toHtml (takeWhile (/= ':') $ problem p)
                                        B.td $ B.toHtml (drop 1 . dropWhile (/= ':') $ problem p)
                                        B.td $ B.toHtml (dateDisplay (submitted p) course)
                                        B.td $ B.toHtml $ show $ score

tryDelete name = "tryDeleteRule(\"" <> name <> "\")"

--properly localized assignments for a given class 
--XXX---should this just be in the hamlet?
assignmentsOf cid textbookproblems = do
             asmd <- runDB $ selectList [AssignmentMetadataCourse ==. cid] []
             Just course <- runDB $ get cid
             return $
                [whamlet|
                <table.table.table-striped>
                    <thead>
                        <th> Assignment
                        <th> Due Date
                    <tbody>
                        $maybe dd <- textbookproblems
                            $forall (num,date) <- IM.toList (readAssignmentTable dd)
                                <tr>
                                    <td>
                                        <a href=@{ChapterR $ chapterOfProblemSet ! num}>
                                            Problem Set #{show num}
                                    <td>
                                        #{dateDisplay date course}
                        $forall a <- map entityVal asmd
                            <tr>
                                <td>
                                    <a href=@{AssignmentR $ assignmentMetadataFilename a}>
                                        #{assignmentMetadataFilename a}
                                $maybe due <- assignmentMetadataDuedate a
                                    <td>#{dateDisplay due course}
                                $nothing
                                    <td>No Due Date
                |]

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
