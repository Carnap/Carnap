module Handler.Instuctor where

import Import
import Util.Data
import Util.Database
import Yesod.Form.Bootstrap3
import Yesod.Form.Jquery
import Handler.User (scoreByIdAndSource)
import Text.Blaze.Html (toMarkup)
import Data.Time
import System.FilePath
import System.Directory (getDirectoryContents,removeFile, doesFileExist)

deleteInstructorR :: Text -> Handler Value
deleteInstructorR _ = do
    fn <- requireJsonBody :: Handler Text
    adir <- assignmentDir 
    deleted <- runDB $ do mk <- getBy $ UniqueAssignment fn
                          case mk of
                              Just (Entity k v) -> do syn <- selectList [SyntaxCheckSubmissionAssignmentId ==. Just k] []
                                                      ders <- selectList [DerivationSubmissionAssignmentId ==. Just k] []
                                                      trans <- selectList [TranslationSubmissionAssignmentId ==. Just k] []
                                                      trutht <- selectList [TruthTableSubmissionAssignmentId ==. Just k] []
                                                      mapM (delete . entityKey) syn
                                                      mapM (delete . entityKey) ders
                                                      mapM (delete . entityKey) trans
                                                      mapM (delete . entityKey) trutht
                                                      delete k
                                                      liftIO $ do fe <- doesFileExist (adir </> unpack fn) 
                                                                  if fe then removeFile (adir </> unpack fn)
                                                                        else return ()
                                                      return True
                              Nothing -> return False
    if deleted 
        then returnJson (fn ++ " deleted")
        else returnJson ("unable to retrieve metadata for " ++ fn)

postInstructorR :: Text -> Handler Html
postInstructorR ident = do
    ((result,widget),enctype) <- runFormPost uploadAssignmentForm
    let maybeclass = instructorCourse <$> instructorData <$> instructorByEmail ident 
    case (result,maybeclass) of 
        (FormSuccess (file, duedate, textarea, subtime), Just theclass) ->
            do let fn = fileName file
               let duetime = UTCTime duedate 0
               let info = unTextarea <$> textarea
               success <- tryInsert $ AssignmentMetadata fn info duetime subtime theclass
               if success then saveAssignment file 
                          else setMessage "Could not save---this file already exists"
        (FormFailure s,_) -> setMessage $ "Something went wrong: " ++ toMarkup (show s)
        (FormMissing,_) -> setMessage "Submission data incomplete"
        _ -> setMessage "something went wrong with the form submission"
    redirect $ InstructorR ident

getInstructorR :: Text -> Handler Html
getInstructorR ident = do
    musr <- runDB $ getBy $ UniqueUser ident
    case musr of 
        Nothing -> defaultLayout nopage
        (Just (Entity uid _))  -> do
            UserData firstname lastname enrolledin _ <- checkUserData uid 
            let maybeclass = instructorCourse <$> instructorData <$> instructorByEmail ident
            case maybeclass of
                Nothing -> defaultLayout nopage
                Just theclass ->
                    do allUserData <- map entityVal <$> (runDB $ selectList [UserDataEnrolledIn ==. theclass] [])
                       let allUids = (map userDataUserId  allUserData)
                       musers <- mapM (\x -> runDB (get x)) allUids
                       let users = catMaybes musers
                       allScores <- mapM (scoreByIdAndSource (sourceOf theclass)) allUids >>= return . zip (map userIdent users)
                       let usersAndData = zip users allUserData
                       assignmentMetadata <- map entityVal <$> listAssignmentMetadata theclass
                       ((_,assignmentWidget),enctype) <- runFormPost uploadAssignmentForm
                       defaultLayout $ do
                         setTitle $ "Instructor Page for " ++ toMarkup firstname ++ " " ++ toMarkup lastname
                         $(widgetFile "instructor")
    where tryLookup l x = case lookup x l of
                          Just n -> show n
                          Nothing -> "can't find scores"
          
          nopage = [whamlet|
                    <div.container>
                        <p> Instructor not found.
                   |]

          tryDelete (AssignmentMetadata fn _ _ _ _) = "tryDeleteAssignment(\"" ++ fn ++ "\")"

uploadAssignmentForm = renderBootstrap3 BootstrapBasicForm $ (,,,)
    <$> fileAFormReq (bfs ("Assignment" :: Text))
    <*> areq (jqueryDayField def) (bfs ("Due Date"::Text)) Nothing
    <*> aopt textareaField (bfs ("Assignment Description"::Text)) Nothing
    <*> lift (liftIO getCurrentTime)

saveAssignment file = do
        let assignmentname = unpack $ fileName file
        path <- assignmentPath assignmentname
        liftIO $ fileMove file path

-- TODO compare directory contents with database results
listAssignmentMetadata theclass = do asmd <- runDB $ selectList [AssignmentMetadataCourse ==. theclass] []
                                     return asmd

assignmentPath f = do dir <- assignmentDir
                      return $ dir </> f

assignmentDir = do master <- getYesod 
                   if appDevel (appSettings master) 
                        then return "assignments"
                        else return "/root/assignments"
