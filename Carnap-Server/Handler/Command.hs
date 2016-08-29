module Handler.Command where

import Import
import Carnap.GHCJS.SharedTypes
import Model (SyntaxCheckSubmission,TranslationSubmission)
import Data.Time 

postCommandR :: Handler Value
postCommandR = do
    cmd  <- requireJsonBody :: Handler GHCJSCommand

    maybeCurrentUserId <- maybeAuthId

    case maybeCurrentUserId of 
           Nothing -> returnJson ("No User" :: String)
           Just u  -> case cmd of
                EchoBack (s,b) -> returnJson (reverse s)
                SubmitSyntaxCheck f -> do success <- submit SyntaxCheckSubmission f u
                                          if success 
                                             then returnJson ("submitted!" :: String)
                                             else returnJson ("Clash" :: String)
                SubmitTranslation f -> do success <- submit TranslationSubmission f u
                                          if success 
                                             then returnJson ("submitted!" :: String)
                                             else returnJson ("Clash" :: String)


submit typ f u = do time <- liftIO getCurrentTime
                    let sub = typ (pack f) (pack $ show time) u
                    runDB $ do munique <- checkUnique sub
                               case munique of 
                                    (Just _) -> return False
                                    Nothing  -> do insert sub
                                                   return True
