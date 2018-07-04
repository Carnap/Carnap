module Handler.Review (getReviewR, putReviewR) where

import Import
import Util.Database
import Text.Read (readMaybe)
import Yesod.Form.Bootstrap3
import Carnap.GHCJS.SharedTypes

putReviewR :: Text -> Handler Value
putReviewR filename =
        do (Entity key val, _) <- getAssignmentByFilename filename
           ((theUpdate,_),_) <- runFormPost (identifyForm "updateSubmission" $ updateSubmissionForm Nothing "" "")
           case theUpdate of
               FormSuccess (ident, serializeduid, extra) -> do
                   success <- runDB $ do case readMaybe serializeduid of 
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
           let problems = sortBy theSorting unsortedProblems
           defaultLayout $ do
               addScript $ StaticR js_popper_min_js
               addScript $ StaticR ghcjs_rts_js
               addScript $ StaticR ghcjs_allactions_lib_js
               addScript $ StaticR ghcjs_allactions_out_js
               addStylesheet $ StaticR css_exercises_css
               $(widgetFile "review")
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
        let ident = problemSubmissionIdent val
            uid = problemSubmissionUserId val
            extra = problemSubmissionExtra val
        (updateSubmissionWidget,enctypeUpdateSubmission) <- generateFormPost (identifyForm "updateSubmission" $ updateSubmissionForm extra ident (show uid))
        case (problemSubmissionType val, problemSubmissionData val) of
            (Derivation, DerivationData content der) ->
                [whamlet|
                    <h4>#{ident}
                    <div>#{content}
                    <pre>#{der}
                    <form.updateSubmission enctype=#{enctypeUpdateSubmission}>
                        ^{updateSubmissionWidget}
                        <div.form-group>
                            <input.btn.btn-primary type=submit value="update">
                |]
            (TruthTable, TruthTableData content tt) -> 
                [whamlet|
                    <h4>#{ident}
                    <div>#{content}
                    <pre>#{show tt}
                    <form.updateSubmission enctype=#{enctypeUpdateSubmission}>
                        ^{updateSubmissionWidget}
                        <div.form-group>
                            <input.btn.btn-primary type=submit value="update">
                |]
            (Translation, TranslationData content trans) -> 
                [whamlet|
                    <h4>#{ident}
                    <div>#{content}
                    <pre>#{trans}
                    <form.updateSubmission enctype=#{enctypeUpdateSubmission}>
                        ^{updateSubmissionWidget}
                        <div.form-group>
                            <input.btn.btn-primary type=submit value="update">
                |]
            _ -> return ()

updateSubmissionForm extra ident uid = renderBootstrap3 BootstrapBasicForm $ (,,)
            <$> areq hiddenField "" (Just ident)
            <*> areq hiddenField "" (Just uid) 
            <*> areq intField (bfs ("Extra Credit Points"::Text)) extra
