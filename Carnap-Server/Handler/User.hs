module Handler.User where

import Import
import qualified Text.Blaze.Html5 as B

getUserR :: Text -> Handler Html
getUserR userId = do
    cmmts <- yourComments userId
    synsubs <- yourSynSubs userId
    defaultLayout $ do
        setTitle "Welcome To Your Homepage!"
        [whamlet|
            <p> Ker boop #{userId}
            <p> #{textToUl cmmts}
            <p> #{textToUl synsubs}
            <a href=@{AuthR LogoutR}>
                Logout
        |]

textToUl :: [Text] -> Html
textToUl xs = do B.ul $ mapM_ (B.li . B.toHtml) xs

yourComments userId = do cmmts <- runDB $ selectList [] []
                         let pairs = map (toPair . fromEnt) cmmts
                         cpairs <- mapM clean pairs
                         return $ map snd $ filter (\(x,_) -> x == userId) cpairs

    where toPair (Comment msg mu)  = (mu, msg)

yourSynSubs  userId = do subs <- runDB $ selectList [] []
                         let pairs = map (toPair . fromEnt) subs
                         cpairs <- mapM clean pairs
                         return $ map snd $ filter (\(x,_) -> x == userId) cpairs

    where toPair (SyntaxCheckSubmission prob time pu)  = (pu,prob)

clean :: (Maybe (Key User), Text) -> Handler (Text,Text)
clean (Nothing, s)  = return ("annonyous", s)
clean (Just sid, s) = do sub <- runDB $ get404 sid
                         return (userIdent sub, s)

fromEnt (Entity k v) = v
