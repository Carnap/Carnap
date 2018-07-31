module Handler.Assignment (getAssignmentR, getFullAssignmentR) where

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

getAssignmentR :: Text -> Handler Html
getAssignmentR filename = getAssignment filename >>= uncurry returnAssignment

getAssignmentByOwnerR :: Text -> Text -> Handler Html
getAssignmentByOwnerR owner filename = getAssignmentByOwner owner filename >>= uncurry returnAssignment

getFullAssignmentR :: Text -> Text -> Text -> Handler Html
getFullAssignmentR coursetitle owner filename = getAssignmentByCourseAndOwner coursetitle owner filename >>= uncurry returnAssignment

returnAssignment :: Entity AssignmentMetadata -> FilePath -> Handler Html
returnAssignment (Entity key val) path = do
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
