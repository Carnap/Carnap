module Handler.Assignment (getAssignmentR,getAssignmentsR) where

import Import
import Util.Data
import Util.Database
import Yesod.Markdown
import System.Directory (doesFileExist,getDirectoryContents)
import Text.Julius (juliusFile,rawJS)
import Text.Pandoc.Walk (walkM, walk)
import Filter.SynCheckers
import Filter.ProofCheckers
import Filter.Translate
import Filter.TruthTables

getAssignmentsR :: Handler Html
getAssignmentsR = do muid <- maybeAuthId
                     ud <- case muid of
                                 Nothing -> 
                                    do setMessage "you need to be logged in to access assignments"
                                       redirect HomeR
                                 Just uid -> checkUserData uid
                     (course,cid) <- case userDataEnrolledIn ud of
                                      Just cid -> do Just course <- runDB $ get cid
                                                     return (course,cid)
                                      Nothing -> do setMessage "you need to be enrolled in a course to access assignments"
                                                    redirect HomeR
                     Entity _ instructor <- udByInstructorId $ courseInstructor course
                     Just instructorident <- getIdent (userDataUserId instructor)
                     time <- liftIO getCurrentTime
                     assignmentMD <- runDB $ selectList 
                                                ([AssignmentMetadataCourse ==. cid] 
                                                ++ ([AssignmentMetadataVisibleTill >. Just time] ||. [AssignmentMetadataVisibleTill ==. Nothing])
                                                ++ ([AssignmentMetadataVisibleFrom <. Just time] ||. [AssignmentMetadataVisibleFrom ==. Nothing]))
                                                []
                     adir <- assignmentDir instructorident
                     adirContents <- lift $ getDirectoryContents adir
                     asDocs <- mapM (runDB . get) (map (assignmentMetadataDocument . entityVal) assignmentMD)
                     defaultLayout
                          [whamlet|
                              <div.container>
                                  <h1>Assignments
                                  <ul>
                                      $forall (Entity _ a, Just d) <- zip assignmentMD asDocs
                                          <li>
                                            <div.assignment>
                                                <p>
                                                    <a href=@{AssignmentR $ documentFilename d}>
                                                        #{documentFilename d}
                                                $maybe desc <- assignmentMetadataDescription a
                                                    <p> #{desc}
                                                $nothing
                                                <p>Due: #{show $ assignmentMetadataDuedate a}
                          |]

getAssignmentR :: Text -> Handler Html
getAssignmentR filename = 
        do (Entity key val, path) <- getAssignmentByFilename filename
           time <- liftIO getCurrentTime
           if visibleAt time val 
               then do
                   ehtml <- lift $ fileToHtml path
                   case ehtml of
                       Left err -> defaultLayout $ layout (show err)
                       Right html -> do
                           defaultLayout $ do
                               let source = "assignment:" ++ show key 
                               toWidgetHead $(juliusFile "templates/command.julius")
                               toWidgetHead [julius|var submission_source="#{rawJS source}";|]
                               toWidgetHead [julius|var assignment_key="#{rawJS $ show key}";|]
                               addScript $ StaticR js_popper_min_js
                               addScript $ StaticR ghcjs_rts_js
                               addScript $ StaticR ghcjs_allactions_lib_js
                               addScript $ StaticR ghcjs_allactions_out_js
                               addStylesheet $ StaticR css_tree_css
                               addStylesheet $ StaticR css_exercises_css
                               $(widgetFile "document")
                               addScript $ StaticR ghcjs_allactions_runmain_js
               else defaultLayout $ layout ("assignment not currently available" :: Text)
    where layout c = [whamlet|
                        <div.container>
                            <article>
                                #{c}
                        |]
          visibleAt t a = (assignmentMetadataVisibleTill a > Just t || assignmentMetadataVisibleTill a == Nothing)
                          && (assignmentMetadataVisibleFrom a < Just t || assignmentMetadataVisibleFrom a == Nothing)

fileToHtml path = do Markdown md <- markdownFromFile path
                     let md' = Markdown (filter ((/=) '\r') md) --remove carrage returns from dos files
                     case parseMarkdown yesodDefaultReaderOptions md' of
                         Right pd -> do let pd' = walk allFilters pd
                                        return $ Right $ writePandocTrusted yesodDefaultWriterOptions pd'
                         Left e -> return $ Left e
    where allFilters = (makeSynCheckers . makeProofChecker . makeTranslate . makeTruthTables)
