module Handler.Assignment (getAssignmentR, getCourseAssignmentR) where

import Import
import Util.Data
import Util.Database
import Yesod.Markdown
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

getAssignmentR :: Text -> Handler Html
getAssignmentR filename = getAssignment filename >>= uncurry returnAssignment

getCourseAssignmentR :: Text -> Text -> Handler Html
getCourseAssignmentR coursetitle filename = getAssignmentByCourse coursetitle filename >>= uncurry returnAssignment

returnAssignment :: Entity AssignmentMetadata -> FilePath -> Handler Html
returnAssignment (Entity key val) path = do
           time <- liftIO getCurrentTime
           muid <- maybeAuthId
           mident <- maybe reject getIdent muid 
           classes <- maybe reject classesByInstructorIdent mident 
           if visibleAt time val || assignmentMetadataCourse val `elem` map entityKey classes 
               then do
                   ehtml <- liftIO $ fileToHtml (hash (show muid ++ path)) path
                   unless (visibleAt time val) $ setMessage "Viewing as instructor. Assignment not currently visible to students."
                   case ehtml of
                       Left err -> defaultLayout $ layout (show err)
                       Right (Left err) -> defaultLayout $ layout (show err)
                       Right (Right html) -> do
                           defaultLayout $ do
                               let source = "assignment:" ++ show key 
                               toWidgetHead $(juliusFile "templates/command.julius")
                               toWidgetHead [julius|var submission_source="#{rawJS source}";|]
                               toWidgetHead [julius|var assignment_key="#{rawJS $ show key}";|]
                               addScript $ StaticR js_proof_js
                               addScript $ StaticR js_popper_min_js
                               addScript $ StaticR ghcjs_rts_js
                               addScript $ StaticR ghcjs_allactions_lib_js
                               addScript $ StaticR ghcjs_allactions_out_js
                               addStylesheet $ StaticR css_proof_css
                               addStylesheet $ StaticR css_tree_css
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
          reject = setMessage "you need to be logged in to access assignments" >> redirect HomeR

fileToHtml salt path = do Markdown md <- markdownFromFile path
                          let md' = Markdown (filter ((/=) '\r') md) --remove carrage returns from dos files
                          case parseMarkdown yesodDefaultReaderOptions { readerExtensions = carnapPandocExtensions } md' of
                              Right pd -> do let pd' = walk allFilters pd
                                             return $ Right $ writePandocTrusted yesodDefaultWriterOptions 
                                                             { writerExtensions = carnapPandocExtensions
                                                             , writerWrapText=WrapPreserve } pd'
                              Left e -> return $ Left e
    where allFilters = (randomizeProblems salt . makeSequent . makeSynCheckers . makeProofChecker . makeTranslate . makeTruthTables . makeCounterModelers . makeQualitativeProblems)
