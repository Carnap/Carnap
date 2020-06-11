module Util.Handler where

import Import
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import Text.Pandoc (MetaValue(..),Inline(..))
import Text.Julius (juliusFile,rawJS)
import Text.Hamlet (hamletFile)
import Util.Data
import Util.Database

minimalLayout c = [whamlet|
                  <div.container>
                      <article>
                          #{c}
                  |]

retrieveCss metaval = case metaval of 
                        Just (MetaInlines ils) -> return $ Just (catMaybes (map fromStr ils))
                        Just (MetaList list) -> do mcsses <- mapM retrieveCss (map Just list) 
                                                   return . Just . concat . catMaybes $ mcsses
                        Nothing -> return Nothing
                        x -> setMessage (toHtml ("bad css metadata: " ++ show x)) >> return Nothing
    where fromStr (Str x) = Just x
          fromStr _ = Nothing

customLayout css widget = do
        master <- getYesod
        mmsg <- getMessage
        authmaybe <- maybeAuth
        instructors <- instructorIdentList
        let customLayoutCss = css
        pc <- widgetToPageContent $(widgetFile "default-layout")
        withUrlRenderer $(hamletFile "templates/custom-layout-wrapper.hamlet")
