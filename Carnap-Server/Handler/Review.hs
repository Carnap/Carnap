module Handler.Review (getReviewR, putReviewR) where

import Import
import Util.Database
import Data.Map as M (fromList)
import Data.Tree
import Data.List (nub)
import Text.Read (readMaybe)
import Yesod.Form.Bootstrap3
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.SharedFunctions (simpleCipher)

putReviewR :: Text -> Text -> Handler Value
putReviewR coursetitle filename =
        do (Entity key val, _) <- getAssignmentByCourse coursetitle filename
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

getReviewR :: Text -> Text -> Handler Html
getReviewR coursetitle filename = 
        do (Entity key val, _) <- getAssignmentByCourse coursetitle filename
           unsortedProblems <- runDB $ selectList [ProblemSubmissionAssignmentId ==. Just key] []
           uidAndUser  <- runDB $ do let uids = nub $ map (problemSubmissionUserId . entityVal) unsortedProblems
                                     musers <- mapM get uids
                                     return $ zip musers uids 
           let problems = sortBy theSorting unsortedProblems
           defaultLayout $ do
               addScript $ StaticR js_popper_min_js
               addScript $ StaticR js_proof_js
               addScript $ StaticR ghcjs_rts_js
               addScript $ StaticR ghcjs_allactions_lib_js
               addScript $ StaticR ghcjs_allactions_out_js
               addStylesheet $ StaticR css_proof_css
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

selectUser list = 
        [whamlet|
            <select#selectStudent class="form-control">
                <option value="all">All Students
                $forall (k,v) <- list
                    $maybe k' <- k
                        <option value="#{show v}">#{userIdent k'}
                    $nothing
                        <option value="#{show v}">unknown
        |]


renderProblem (Entity key val) = do
        let ident = problemSubmissionIdent val
            uid = problemSubmissionUserId val
            extra = problemSubmissionExtra val
        (updateSubmissionWidget,enctypeUpdateSubmission) <- generateFormPost (identifyForm "updateSubmission" $ updateSubmissionForm extra ident (show uid))
        let isGraded = case extra of Just _ -> "graded"; _ -> "ungraded" :: String
            template display = 
                [whamlet|
                    <div.card.mb-3.#{isGraded} data-submission-uid="#{show uid}">
                        <div.card-body style="padding:20px">
                            <h4.card-title>#{ident}
                            <div.row>
                                <div.col-sm-8>
                                    ^{display}
                                <div.col-sm-4>
                                    <form.updateSubmission enctype=#{enctypeUpdateSubmission}>
                                        ^{updateSubmissionWidget}
                                        <div.form-group>
                                            <input.btn.btn-primary type=submit value="update">
                |]
        case (problemSubmissionType val, problemSubmissionData val) of
            (Derivation, DerivationData content der) -> template $
                [whamlet|
                    <div data-carnap-system="prop" 
                         data-carnap-options="resize"
                         data-carnap-type="proofchecker"
                         data-carnap-goal="#{content}"
                         data-carnap-submission="none">
                         #{der}
                |]
            (Derivation, DerivationDataOpts content der opts) -> template $
                [whamlet|
                    <div data-carnap-type="proofchecker"
                         data-carnap-system="#{sys}"
                         data-carnap-options="resize"
                         data-carnap-goal="#{content}"
                         data-carnap-submission="none">
                         #{der}
                |]
                where sys = case lookup "system" (M.fromList opts) of Just s -> s; Nothing -> "prop"
            (TruthTable, TruthTableData content tt) -> template $
                [whamlet|
                    <div data-carnap-type="truthtable"
                         data-carnap-tabletype="#{checkvalidity content}"
                         data-carnap-submission="none"
                         data-carnap-goal="#{content}">
                         #{renderTT tt}
                |]
            (TruthTable, TruthTableDataOpts content tt opts) -> template $
                [whamlet|
                    <div data-carnap-type="truthtable"
                         data-carnap-tabletype="#{tabletype}"
                         data-carnap-system="#{ttsystem}"
                         data-carnap-submission="none"
                         data-carnap-options="immutable nocheck nocounterexample"
                         data-carnap-goal="#{formatContent (unpack content)}">
                         #{renderTT tt}
                |]
                where tabletype = case lookup "tabletype" (M.fromList opts) of Just s -> s; Nothing -> checkvalidity content
                      ttsystem = case lookup "system" (M.fromList opts) of Just s -> s; Nothing -> "prop"
                      formatContent c = case (ndNotation `ofPropSys` ttsystem) <*> maybeString of Just s -> s; Nothing -> ""
                        where maybeString = (show <$> (readMaybe c :: Maybe PureForm))
                                    `mplus` (intercalate "," . map show <$> (readMaybe c :: Maybe [PureForm]))
                                    `mplus` case readMaybe c :: Maybe ([PureForm],[PureForm]) of
                                                      Just (fs,gs) -> Just $ intercalate "," (map show fs) ++ ":" ++ intercalate "," (map show gs)
                                                      Nothing -> Just c --If it's a sequent, it'll show properly anyway.

            (CounterModel, CounterModelDataOpts content cm opts) -> template $
                [whamlet|
                    <div data-carnap-type="countermodeler"
                         data-carnap-countermodelertype="#{cmtype}"
                         data-carnap-submission="none"
                         data-carnap-system="#{cmsystem}"
                         data-carnap-goal="#{formatContent (unpack content)}">
                         #{renderCM cm}
                |]
                where cmtype = case lookup "countermodelertype" (M.fromList opts) of Just s -> s; Nothing -> checkvalidity content
                      cmsystem = case lookup "system" (M.fromList opts) of Just s -> s; Nothing -> "firstOrder"
                      formatContent c = case (ndNotation `ofFOLSys` cmsystem) <*> maybeString of Just s ->  s; Nothing -> ""
                        where maybeString = (show <$> (readMaybe c :: Maybe PureForm))
                                    `mplus` (intercalate "," . map show <$> (readMaybe c :: Maybe [PureFOLForm]))
                                    `mplus` Just c --If it's a sequent, it'll show properly anyway.

            (Translation, TranslationData content trans) -> template $
                [whamlet|
                    <div data-carnap-type="translate"
                         data-carnap-transtype="prop"
                         data-carnap-goal="#{show (simpleCipher (unpack content))}"
                         data-carnap-submission="none"
                         data-carnap-problem="#{content}">
                         #{trans}
                |]

            (SequentCalc, SequentCalcData content tree opts) -> template $
                [whamlet|
                    <div data-carnap-type="sequentchecker"
                         data-carnap-system="#{sys}"
                         data-carnap-options="resize"
                         data-carnap-goal="#{content}"
                         data-carnap-submission="none">
                         #{seqJSON tree}
                |]
                where sys = case lookup "system" (M.fromList opts) of Just s -> s; Nothing -> "propLK"
                      seqJSON (Node (l,r) f) = "{\"label\":\"" ++ l 
                                             ++ "\",\"rule\":\"" ++ r
                                             ++ "\",\"forest\":[" ++ concatMap seqJSON f
                                             ++ "]}"
            (Translation, TranslationDataOpts content trans opts) -> template $
                [whamlet|
                    <div data-carnap-type="translate"
                         data-carnap-transtype="#{transtype}"
                         data-carnap-goal="#{show (simpleCipher (unpack content))}"
                         data-carnap-submission="none"
                         data-carnap-problem="#{problem}">
                         #{trans}
                |]
                where transtype = case lookup "transtype" (M.fromList opts) of Just s -> s; Nothing -> "prop"
                      problem = case lookup "problem" (M.fromList opts) of Just s -> s ++ " : " ++ (unpack content)
            _ -> return ()
    where renderTT tt = concat $ map renderRow tt
          renderRow row = map toval row ++ "\n"
          toval (Just True) = 'T'
          toval (Just False) = 'F'
          toval Nothing = '-'
          checkvalidity ct = if '⊢' `elem` ct then "validity" :: String else "simple" :: String
          renderCMPair (l,v) = l ++ ":" ++ v
          renderCM cm = unlines . map renderCMPair $ cm

updateSubmissionForm extra ident uid = renderBootstrap3 BootstrapBasicForm $ (,,)
            <$> areq hiddenField "" (Just ident)
            <*> areq hiddenField "" (Just uid) 
            <*> areq intField (bfs ("Partial Credit Points"::Text)) extra
