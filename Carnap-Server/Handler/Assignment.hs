module Handler.Assignment (getAssignmentR, postCourseAssignmentR, getCourseAssignmentR) where

import Import
import Util.Data
import Util.Database
import Yesod.Markdown
import Yesod.Form.Bootstrap3
import Text.Blaze.Html (toMarkup)
import Text.Pandoc (writerExtensions,writerWrapText, WrapOption(..), readerExtensions)
import System.Directory (doesFileExist,getDirectoryContents)
import Text.Julius (juliusFile,rawJS)
import Text.Pandoc.Walk (walkM, walk)
import Filter.Randomize
import Filter.SynCheckers
import Filter.ProofCheckers
import Filter.Translate
import Filter.TruthTables
import Filter.CounterModelers
import Filter.Qualitative
import Filter.Sequent
import Filter.TreeDeduction
import Filter.RenderFormulas

getAssignmentR :: Text -> Handler Html
getAssignmentR filename = getAssignment filename >>= uncurry returnAssignment

getCourseAssignmentR :: Text -> Text -> Handler Html
getCourseAssignmentR coursetitle filename = getAssignmentByCourse coursetitle filename >>= uncurry returnAssignment

postCourseAssignmentR :: Text -> Text -> Handler Html
postCourseAssignmentR coursetitle filename = do
            ((Entity key val), _) <- getAssignmentByCourse coursetitle filename
            muid <- maybeAuthId
            uid <- maybe reject return muid
            ((passrslt,_),_) <- runFormPost (identifyForm "enterPassword" $ enterPasswordForm)
            case passrslt of 
                FormSuccess password -> 
                    let insertToken = do currentTime <- liftIO getCurrentTime
                                         runDB $ insert $ AssignmentAccessToken currentTime key uid
                                         setMessage $ "Access Granted"
                                         return ()
                    in case assignmentMetadataAvailability val of
                            Just (ViaPassword thepwd) | password == thepwd -> insertToken
                            Just (HiddenViaPassword thepwd) | password == thepwd -> insertToken
                            _ -> setMessage $ "Incorrect Access Key"
                FormFailure s -> setMessage $ "Something went wrong: " ++ toMarkup (show s)
                FormMissing -> setMessage $ "Form Missing"
            redirect $ CourseAssignmentR coursetitle filename

returnAssignment :: Entity AssignmentMetadata -> FilePath -> Handler Html
returnAssignment (Entity key val) path = do
           time <- liftIO getCurrentTime
           muid <- maybeAuthId
           uid <- maybe reject return muid
           mident <- getIdent uid
           classes <- maybe reject classesByInstructorIdent mident
           mtoken <- runDB $ getBy $ UniqueAssignmentAccessToken uid key
           let instructorAccess = assignmentMetadataCourse val `elem` map entityKey classes
           if visibleAt time val || instructorAccess 
               then do
                   ehtml <- liftIO $ fileToHtml (hash (show muid ++ path)) path
                   unless (visibleAt time val) $ setMessage "Viewing as instructor. Assignment not currently visible to students."
                   case ehtml of
                       Left err -> defaultLayout $ layout (show err)
                       Right (Left err) -> defaultLayout $ layout (show err)
                       Right (Right html) -> case (assignmentMetadataAvailability val, mtoken) of
                           (Just (ViaPassword pass), Nothing) -> defaultLayout $ do
                               (enterPasswordWidget,enctypeEnterPassword) <- generateFormPost (identifyForm "enterPassword" $ enterPasswordForm)
                               $(widgetFile "passwordEntry") 
                           (Just (HiddenViaPassword pass), Nothing) -> defaultLayout $ do
                               (enterPasswordWidget,enctypeEnterPassword) <- generateFormPost (identifyForm "enterPassword" $ enterPasswordForm)
                               $(widgetFile "passwordEntry") 
                           (_,_) -> defaultLayout $ do
                               let source = "assignment:" ++ show key 
                               toWidgetHead $(juliusFile "templates/command.julius")
                               toWidgetHead $(juliusFile "templates/status-warning.julius")
                               toWidgetHead [julius|var submission_source="#{rawJS source}";|]
                               toWidgetHead [julius|var assignment_key="#{rawJS $ show key}";|]
                               addScript $ StaticR js_proof_js
                               addScript $ StaticR js_popper_min_js
                               addScript $ StaticR ghcjs_rts_js
                               addScript $ StaticR ghcjs_allactions_lib_js
                               addScript $ StaticR ghcjs_allactions_out_js
                               addStylesheet $ StaticR css_proof_css
                               addStylesheet $ StaticR css_tree_css
                               addStylesheet $ StaticR css_bootstrapextra_css
                               addStylesheet $ StaticR css_exercises_css
                               $(widgetFile "document")
                               addScript $ StaticR ghcjs_allactions_runmain_js
               else defaultLayout $ layout ("Assignment not currently set as visible by instructor" :: Text)
    where layout c = [whamlet|
                        <div.container>
                            <article>
                                #{c}
                        |]
          visibleAt t a = (assignmentMetadataVisibleTill a > Just t || assignmentMetadataVisibleTill a == Nothing)
                          && (assignmentMetadataVisibleFrom a < Just t || assignmentMetadataVisibleFrom a == Nothing)

fileToHtml salt path = do Markdown md <- markdownFromFile path
                          let md' = Markdown (filter ((/=) '\r') md) --remove carrage returns from dos files
                          case parseMarkdown yesodDefaultReaderOptions { readerExtensions = carnapPandocExtensions } md' of
                              Right pd -> do let pd' = walk allFilters pd
                                             return $ Right $ writePandocTrusted yesodDefaultWriterOptions 
                                                             { writerExtensions = carnapPandocExtensions
                                                             , writerWrapText=WrapPreserve } pd'
                              Left e -> return $ Left e
    where allFilters = randomizeProblems salt . makeTreeDeduction . makeSequent . makeSynCheckers . makeProofChecker . makeTranslate . makeTruthTables . makeCounterModelers . makeQualitativeProblems . renderFormulas

enterPasswordForm = renderBootstrap3 BootstrapBasicForm $ id
            <$> areq textField (bfs ("Access Key" :: Text)) Nothing

reject = setMessage "you need to be logged in to access assignments" >> redirect HomeR
