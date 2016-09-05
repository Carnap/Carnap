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
                SubmitSyntaxCheck f -> submit SyntaxCheckSubmission f u >>= afterInsert
                SubmitTranslation f -> submit TranslationSubmission f u >>= afterInsert
                SubmitDerivation s d -> do time <- liftIO getCurrentTime               
                                           let sub = DerivationSubmission (pack s) (pack d) (pack $ show time) u 
                                           tryInsert sub >>= afterInsert

submit typ f u = do time <- liftIO getCurrentTime
                    let sub = typ (pack f) (pack $ show time) u
                    tryInsert sub

tryInsert sub = runDB $ do munique <- checkUnique sub       
                           case munique of                  
                                (Just _) -> return False    
                                Nothing  -> do insert sub   
                                               return True

afterInsert success = if success then returnJson ("submitted!" :: String) else returnJson ("Clash" :: String)
