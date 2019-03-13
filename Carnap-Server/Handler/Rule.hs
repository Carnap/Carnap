module Handler.Rule where

import Import
import Text.Julius (juliusFile)
import Text.Hamlet (hamletFile)
import Carnap.GHCJS.SharedTypes
import Data.Aeson (decodeStrict)
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes

getRuleR :: Handler Html
getRuleR = do derivedRules <- getDrList
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
                                $maybe rules <- derivedRules
                                    <div.derivedRules>
                                        <h2> My Derived Rules
                                        #{rules}
                                $nothing
                                <div.ruleBuilder>
                                    <h2>The Rule Builder
                                    <div data-carnap-type="proofchecker" 
                                         data-carnap-system="prop" 
                                         data-carnap-submission="saveRule">
                            |]

ruleLayout widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        pc     <- widgetToPageContent $ do
            toWidgetHead $(juliusFile "templates/command.julius")
            addScript $ StaticR ghcjs_rts_js
            addScript $ StaticR ghcjs_allactions_lib_js
            addScript $ StaticR ghcjs_allactions_out_js
            addStylesheet $ StaticR css_tree_css
            addStylesheet $ StaticR css_tufte_css
            addStylesheet $ StaticR css_tuftextra_css
            addStylesheet $ StaticR css_exercises_css
            $(widgetFile "default-layout")
            addScript $ StaticR ghcjs_allactions_runmain_js
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")

getDrList = do maybeCurrentUserId <- maybeAuthId
               case maybeCurrentUserId of
                   Nothing -> return Nothing
                   Just u -> do savedRules <- runDB $ selectList [SavedDerivedRuleUserId ==. u] []
                                return $ Just (formatRules (map entityVal savedRules))

formatRules rules = B.table B.! class_ "rules" $ do
        B.thead $ do
            B.th "Name"
            B.th "Premises"
            B.th "Conclusion"
        B.tbody $ mapM_ toRow rules
    where toRow (SavedDerivedRule dr n _ _) = let (Just dr') = decodeStrict dr in 
                                              B.tr $ do B.td $ B.toHtml $ "D-" ++ n
                                                        B.td $ B.toHtml $ intercalate "," $ map show $ premises dr'
                                                        B.td $ B.toHtml $ show $ conclusion dr'
