module Handler.Review (getReviewR) where

import Import
import Util.Database
import Text.Read (readMaybe)
import Yesod.Form.Bootstrap3
import Carnap.GHCJS.SharedTypes

putReviewR :: Text -> Handler Value
putReviewR filename =
        do (Entity key val, _) <- getAssignmentByFilename filename
           ((theUpdate,_),_) <- runFormPost (identifyForm "updateSubmission" $ updateSubmissionForm)
           case theUpdate of
               FormSuccess (ident, serializeduid, extra) -> do
                   success <- runDB $ do case readMaybe (unpack serializeduid) of 
                                               Just uid -> do msub <- getBy (UniqueProblemSubmission ident uid (Assignment (show key)))
                                                              case msub of 
                                                                   Just (Entity k _) -> update k [ProblemSubmissionExtra =. Just extra] >> return True
                                                                   Nothing -> return False
                                               Nothing -> return False
                   if success then returnJson ("success" :: Text) else returnJson ("error: no submission record" :: Text)
               FormMissing -> returnJson ("no form" :: Text)
               (FormFailure s) -> returnJson ("error:" <> concat s :: Text)

getReviewR :: Text -> Handler Html
getReviewR filename = 
        do (Entity key val, _) <- getAssignmentByFilename filename
           unsortedProblems <- runDB $ selectList [ProblemSubmissionAssignmentId ==. Just key] []
           (updateSubmissionWidget,enctypeUpdateSubmission) <- generateFormPost (identifyForm "updateSubmission" $ updateSubmissionForm)
           let problems = sortBy theSorting unsortedProblems
           defaultLayout $ do
               addScript $ StaticR js_popper_min_js
               addScript $ StaticR ghcjs_rts_js
               addScript $ StaticR ghcjs_allactions_lib_js
               addScript $ StaticR ghcjs_allactions_out_js
               addStylesheet $ StaticR css_exercises_css
               [whamlet|
               <div.container>
                   <article>
                       $if null problems
                            <p> Nothing to review!
                       $else
                            $forall p <- problems
                                ^{renderProblem p}
                                <form enctype=#{enctypeUpdateSubmission}>
                                    ^{updateSubmissionWidget}
                                    <div.form-group>
                                        <input.btn.btn-primary type=submit value="update">
               |]
               addScript $ StaticR ghcjs_allactions_runmain_js
    where theSorting p p' = scompare s s'
              where s = unpack . problemSubmissionIdent . entityVal $ p
                    s' = unpack . problemSubmissionIdent . entityVal $ p'
                    scompare a a' = case (break (== '.') a, break (== '.') a')  of
                                      ((h,[]),(h',[])) | compare (length h) (length h') /= EQ -> compare (length h) (length h')
                                                       | compare h h' /= EQ -> compare h h' 
                                                       | otherwise -> EQ
                                      ((h,t), (h',t')) | compare (length h) (length h') /= EQ -> compare (length h) (length h')
                                                       | compare h h' /= EQ -> compare h h' 
                                                       | otherwise -> scompare (drop 1 t) (drop 1 t')

renderProblem (Entity key val) = do
        case (problemSubmissionType val, problemSubmissionData val) of
            (Derivation, DerivationData content der) ->
                [whamlet|
                    <h4>#{problemSubmissionIdent val}
                    <div>#{content}
                    <pre>#{der}
                |]
            (TruthTable, TruthTableData content tt) -> 
                [whamlet|
                    <h4>#{problemSubmissionIdent val}
                    <div>#{content}
                    <pre>#{show tt}
                |]
            (Translation, TranslationData content trans) -> 
                [whamlet|
                    <h4>#{problemSubmissionIdent val}
                    <div>#{content}
                    <pre>#{trans}
                |]
            _ -> return ()

updateSubmissionForm = renderBootstrap3 BootstrapBasicForm $ (,,)
            <$> areq identField "" Nothing
            <*> areq uidField "" Nothing
            <*> areq intField (bfs ("Extra Credit Points"::Text)) Nothing
    where identField :: (Monad m, RenderMessage (HandlerSite m) FormMessage) => Field m Text 
          identField = hiddenField
          uidField :: (Monad m, RenderMessage (HandlerSite m) FormMessage) => Field m Text
          uidField = hiddenField
