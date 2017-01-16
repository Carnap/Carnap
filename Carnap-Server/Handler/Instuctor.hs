module Handler.Instuctor where

import Import
import Util.Data
import Util.Database
import Yesod.Form.Bootstrap3
import Handler.User (scoreById)
import Text.Blaze.Html (toMarkup)
import System.FilePath
import System.Directory (getDirectoryContents)


postInstructorR :: Text -> Handler Html
postInstructorR ident = do
    ((result,widget),enctype) <- runFormPost uploadAssignmentForm
    case result of 
        FormSuccess (file, info, date) ->
            do filename <- saveAssignment file
               redirect $ InstructorR ident
        FormFailure _ -> redirect $ InstructorR ident
        FormMissing -> redirect $ InstructorR ident

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
                    do let pointsAvailable = "725" :: Text
                       allUserdataEnt <- runDB $ selectList [UserDataEnrolledIn ==. theclass] []
                       musers <- mapM (\x -> runDB (get x)) (map (userDataUserId . entityVal) allUserdataEnt)
                       let users = catMaybes musers
                       allScores <- mapM scoreById (map (userDataUserId . entityVal) allUserdataEnt)
                                       >>= return . zip (map userIdent users)
                       savedassignments <- listAssignments
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
          getClass "gleachkr@gmail.com" = Just KSUSymbolicI2016
          getClass _ = Nothing

uploadAssignmentForm = renderBootstrap3 BootstrapBasicForm $ (,,)
    <$> fileAFormReq "Assignment"
    <*> aopt textareaField "Assignment Description" Nothing
    <*> lift (liftIO getCurrentTime)

saveAssignment file = do
        let assignmentname = unpack $ fileName file
        path <- assignmentPath assignmentname
        liftIO $ fileMove file path
        return assignmentname

listAssignments = do theDir <- assignmentDir
                     acontents <- liftIO $ getDirectoryContents theDir
                     let assignments = filter (\x -> not (x `elem` [".",".."])) acontents
                     return assignments
        

assignmentPath f = do dir <- assignmentDir
                      return $ dir </> f

assignmentDir = do master <- getYesod 
                   if appDevel (appSettings master) 
                        then return "assignments"
                        else return "/root/assignments"
