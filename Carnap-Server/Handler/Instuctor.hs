module Handler.Instuctor where

import Import
import Util.Data
import Util.Database
import Yesod.Form.Bootstrap3
import Yesod.Form.Jquery
import Handler.User (scoreById)
import Text.Blaze.Html (toMarkup)
import Data.Time
import System.FilePath
import System.Directory (getDirectoryContents)

postInstructorR :: Text -> Handler Html
postInstructorR ident = do
    ((result,widget),enctype) <- runFormPost uploadAssignmentForm
    let maybeclass = getClass ident
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
            UserData firstname lastname enrolledin _ <- checkUserData ident uid 
            let maybeclass = getClass ident
            case maybeclass of
                Nothing -> defaultLayout nopage
                Just theclass ->
                    do allUserData <- map entityVal <$> (runDB $ selectList [UserDataEnrolledIn ==. theclass] [])
                       let allUids = (map userDataUserId  allUserData)
                       musers <- mapM (\x -> runDB (get x)) allUids
                       let users = catMaybes musers
                       allScores <- mapM scoreById allUids >>= return . zip (map userIdent users)
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

          pointsByClass KSUSymbolicI2016 = 725
          pointsByClass Birmingham2017 = 0

getClass "gleachkr@gmail.com" = Just KSUSymbolicI2016
getClass "florio.2@buckeyemail.osu.edu" = Just Birmingham2017
getClass _ = Nothing

uploadAssignmentForm = renderBootstrap3 BootstrapBasicForm $ (,,,)
    <$> fileAFormReq "Assignment"
    <*> areq (jqueryDayField def) "Due Date" Nothing
    <*> aopt textareaField "Assignment Description" Nothing
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
