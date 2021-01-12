module Handler.Rule where

import Import
import Text.Julius (juliusFile)
import Text.Hamlet (hamletFile)
import TH.RelativePaths (pathRelativeToCabalPackage)
import Carnap.GHCJS.SharedTypes
import Util.Database
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes

getRuleR :: Handler Html
getRuleR = do derivedPropRules <- getPropDrList
              derivedFOLRules <- getFOLDrList
              ruleLayout $ [whamlet|
                            <div.container>
                                <h1> Index of Basic Propositional Rules
                                <table.rules>
                                    <thead> <th> Name </th> <th> Premises </th><th> Conclusion </th>
                                    <tbody>
                                        <tr> <td> MP  </td> <td> φ, φ→ψ </td> <td> ψ </td
                                        <tr> <td> MT  </td> <td> ¬ψ, φ→ψ </td> <td> ¬φ </td>
                                        <tr> <td> DNE </td> <td> ¬¬φ </td> <td> φ </td>
                                        <tr> <td> DNI </td> <td> φ </td> <td> ¬¬φ </td>
                                        <tr> <td> S   </td> <td> φ∧ψ </td> <td> φ </td>
                                        <tr> <td> S   </td> <td> φ∧ψ </td> <td> ψ </td>
                                        <tr> <td> ADJ </td> <td> φ, ψ </td> <td> φ∧ψ </td>
                                        <tr> <td> MTP </td> <td> φ∨ψ, ¬φ </td> <td> ψ </td>
                                        <tr> <td> MTP </td> <td> φ∨ψ, ¬ψ </td> <td> φ </td>
                                        <tr> <td> ADD </td> <td> φ </td> <td> φ∨ψ </td>
                                        <tr> <td> ADD </td> <td> ψ </td> <td> φ∨ψ </td>
                                        <tr> <td> BC  </td> <td> ψ↔φ </td> <td> ψ→φ  </td>
                                        <tr> <td> BC  </td> <td> ψ↔φ </td> <td> φ→ψ  </td>
                                        <tr> <td> CB  </td> <td> ψ→φ, φ→ψ  </td> <td> φ↔ψ </td>
                                <h1> Index of Basic Predicate Rules
                                <table.rules>
                                    <thead> <th> Name </th> <th> Premises </th><th> Conclusion </th>
                                    <tbody>
                                        <tr> <td> UI </td> <td> ∀xφ<sub>x</sub> </td> <td> φ<sub>x</sub>(c) </td
                                        <tr> <td> EG </td> <td> φ<sub>x</sub>(c) </td> <td> ∃xφ<sub>x</sub> </td>
                                <h1> Index of Derived Rules
                                $maybe propRules <- derivedPropRules
                                    <div.derivedRules>
                                        <h2> Propositional Rules
                                        <table.rules>
                                            <thead>
                                                <tr>
                                                    <th>Name
                                                    <th>Premises
                                                    <th>Conclusion
                                            <tbody>
                                                $forall rule <- propRules
                                                    #{rule}
                                $nothing
                                <div.ruleBuilder>
                                    <h2>The Propositional Rule Builder
                                    <div data-carnap-type="proofchecker"
                                         data-carnap-system="prop"
                                         data-carnap-guides="montague"
                                         data-carnap-options="resize"
                                         data-carnap-submission="saveRule">

                                $maybe folRules <- derivedFOLRules
                                    <div.derivedRules>
                                        <h2> First-Order Rules
                                        #{folRules}
                                $nothing
                                    <hr.hrSep>
                                <div.ruleBuilder>
                                    <h2>The First-Order Rule Builder
                                    <div data-carnap-type="proofchecker"
                                         data-carnap-system="firstOrder"
                                         data-carnap-guides="montague"
                                         data-carnap-options="resize"
                                         data-carnap-submission="saveRule">
                            |]

ruleLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        (isInstructor, mdoc, mcourse) <- case authmaybe of
            Nothing -> return (False, Nothing, Nothing)
            Just uid -> runDB $ do
                mud <- getBy $ UniqueUserData $ entityKey uid
                mcour <- maybe (return Nothing) get (mud >>= userDataEnrolledIn . entityVal)
                masgn <- maybe (return Nothing) get (mcour >>= courseTextBook)
                mdoc <- maybe (return Nothing) get (assignmentMetadataDocument <$> masgn)
                return (not $ null (mud >>= userDataInstructorId . entityVal), mdoc, mcour)
        pc <- widgetToPageContent $ do
            toWidgetHead $(juliusFile =<< pathRelativeToCabalPackage "templates/command.julius")
            addScript $ StaticR ghcjs_rts_js
            addScript $ StaticR ghcjs_allactions_lib_js
            addScript $ StaticR ghcjs_allactions_out_js
            addStylesheet $ StaticR css_tree_css
            addStylesheet $ StaticR css_tufte_css
            addStylesheet $ StaticR css_tuftextra_css
            addStylesheet $ StaticR css_exercises_css
            $(widgetFile "default-layout")
            addScript $ StaticR ghcjs_allactions_runmain_js
        withUrlRenderer $(hamletFile =<< pathRelativeToCabalPackage "templates/default-layout-wrapper.hamlet")

getPropDrList = do maybeCurrentUserId <- maybeAuthId
                   case maybeCurrentUserId of
                       Nothing -> return Nothing
                       Just uid -> do savedRulesOld <- getDerivedRules uid
                                      savedRules <- getRules uid
                                      return $ Just $ formatOldPropRules savedRulesOld ++ formatPropRules savedRules

getFOLDrList = do maybeCurrentUserId <- maybeAuthId
                  case maybeCurrentUserId of
                       Nothing -> return Nothing
                       Just uid -> Just . formatFOLRules <$> getRules uid


formatOldPropRules rules = map toRow rules
    where toRow (SavedDerivedRule dr n _ _) = let (Just dr') = decodeRule dr in
                                              B.tr $ do B.td $ B.toHtml $ "D-" ++ n
                                                        B.td $ B.toHtml $ intercalate "," $ map show $ premises dr'
                                                        B.td $ B.toHtml $ show $ conclusion dr'
          toRuow _ = return ()

formatPropRules rules = map toRow rules
    where toRow (SavedRule (PropRule dr) n _ _) = B.tr $ do B.td $ B.toHtml $ "D-" ++ n
                                                            B.td $ B.toHtml $ intercalate "," $ map show $ premises dr
                                                            B.td $ B.toHtml $ show $ conclusion dr
          toRow _ = return ()

formatFOLRules rules = B.table B.! class_ "rules" $ do
        B.thead $ do
            B.th "Name"
            B.th "Premises"
            B.th "Conclusion"
        B.tbody $ mapM_ toRow rules
    where toRow (SavedRule (FOLRule dr) n _ _) = B.tr $ do B.td $ B.toHtml $ "D-" ++ n
                                                           B.td $ B.toHtml $ intercalate "," $ map show $ premises dr
                                                           B.td $ B.toHtml $ show $ conclusion dr
          toRow _ = return ()
