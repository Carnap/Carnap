module Handler.Rule where

import Import
import Text.Julius (juliusFile)
import Text.Hamlet (hamletFile)
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.GHCJS.SharedTypes
import Data.Aeson (decodeStrict)
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import qualified Text.Blaze.Html5 as B

getRuleR :: Handler Html
getRuleR = do derivedRules <- getDrList
              ruleLayout $ [whamlet|
                            <div.container>
                                <h1> Rule Lab
                                In the rule lab, you can define and save new rules.<br>
                                <div.ruleBuilder class="proofchecker ruleMaker">
                                    <div.goal>
                                    <textarea>
                                    <div.output>
                                $maybe rules <- derivedRules
                                    <div.derivedRules>
                                        <h3> My Derived Rules
                                        #{rules}
                                $nothing
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
            $(widgetFile "default-layout")
            addScript $ StaticR ghcjs_allactions_runmain_js
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")

getDrList = do maybeCurrentUserId <- maybeAuthId
               case maybeCurrentUserId of
                   Nothing -> return Nothing
                   Just u -> do savedRules <- runDB $ selectList [SavedDerivedRuleUserId ==. u] []
                                return $ Just (formatRules (map entityVal savedRules))

formatRules rules = B.table $ do
        B.thead $ do
            B.th "Name"
            B.th "Premises"
            B.th "Conclusion"
        B.tbody $ mapM_ toRow rules
    where toRow (SavedDerivedRule dr n _ _) = let (Just dr') = decodeStrict dr in 
                                              B.tr $ do B.td $ B.toHtml n
                                                        B.td $ B.toHtml $ show $ premises dr'
                                                        B.td $ B.toHtml $ show $ conclusion dr'
