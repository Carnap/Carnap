module Handler.User where

import Import
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes

getUserR :: Text -> Handler Html
getUserR userId = do
    synsubs <- yourSynSubs userId
    defaultLayout $ do
        setTitle "Welcome To Your Homepage!"
        [whamlet|
            <div.container>
                <h1> Homepage for #{userId}
                <p> This is your homepage, where you can keep track of your progress in the course, and find other useful information.
                <h2> Syntax Checking
                <p> #{subPairToTable synsubs}
                <a href=@{AuthR LogoutR}>
                    Logout
        |]

textToUl :: [Text] -> Html
textToUl xs = do B.ul $ mapM_ (B.li . B.toHtml) xs

subPairToTable :: [(Text,Text)] -> Html
subPairToTable xs = B.table B.! class_ "table table-striped" $ do
                        B.thead $ do
                            B.th "Exercise"
                            B.th "Submission time"
                        B.tbody $ mapM_ toRow xs
        where toRow (x,y) = B.tr $ do B.td $ B.toHtml x
                                      B.td $ B.toHtml y

-- yourComments userId = do cmmts <- runDB $ selectList [] []
--                          let pairs = map (toPair . fromEnt) cmmts
--                          cpairs <- mapM clean pairs
--                          return $ map snd $ filter (\(x,_) -> x == userId) cpairs

--     where toPair (Comment msg mu)  = (mu, msg)

yourSynSubs  userId = do subs <- runDB $ selectList [] []
                         let pairs = map (toPair . fromEnt) subs
                         cpairs <- mapM clean pairs
                         let upairs = filter (\(x,_,_) -> x == userId) cpairs
                         return $ map (\(_,x,y) -> (x,y)) upairs

    where toPair (SyntaxCheckSubmission prob time pu)  = (pu,prob,time)

clean :: (Maybe (Key User), Text, Text) -> Handler (Text,Text,Text)
clean (Nothing, s,s')  = return ("annonyous", s,s')
clean (Just sid, s,s') = do sub <- runDB $ get404 sid
                            return (userIdent sub, s,s')

fromEnt (Entity k v) = v
