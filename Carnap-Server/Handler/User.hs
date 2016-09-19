module Handler.User where

import Import
import Prelude (read)
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Data.Time
import qualified Data.Map as M

getUserR :: Text -> Handler Html
getUserR userId = do
    (synsubs, transsubs,dersubs) <- subsById userId
    let isAdmin = userId == "gleachkr@gmail.com"
    let pointsAvailable = "325" :: Text
    allUsers <- if isAdmin 
                    then (runDB $ selectList [] []) >>= return . (map $ userIdent . entityVal)
                    else return []
    allScores <- mapM scoreById allUsers >>= return . zip allUsers
    defaultLayout $ do
        setTitle "Welcome To Your Homepage!"
        [whamlet|
            <div.container>
                <h1> Homepage for #{userId}
                $if isAdmin
                    <h2> Admin Panel
                    <table class="table table-striped">
                        <thead>
                            <th> Student
                            <th> Total Score
                        <tbody>
                            $forall id' <- allUsers
                                <tr>
                                    <td>
                                        <a href="@{UserR id'}">#{id'}
                                    <td>
                                        #{tryLookup allScores id'}/#{pointsAvailable}
                <p> This is your homepage, where you can keep track of your progress in the course, and find other useful information.
                <h3 style="padding-top:10pt"> Completed Problems
                <h4> Syntax Checking
                #{exPairToTable synsubs}
                <h4> Translation
                #{exPairToTable transsubs}
                <h4> Derivation
                #{exPairToTable dersubs}
                <div.row>
                    <div.col-md-9 style="padding-right:30pt">
                        <h3> Due Dates
                        #{dueDateTable}
                    <div.col-md-3>
                        <h3> Total Points Earned
                        <span style="font-size:56pt; color:gray; padding-left:20pt">
                            #{totalScore (synsubs ++ (transsubs ++ dersubs))}/#{pointsAvailable}
                <div>
                <a href=@{AuthR LogoutR}>
                    Logout
        |]
    where tryLookup l x = case lookup x l of
                          Just n -> show n
                          Nothing -> "can't find scores"

--------------------------------------------------------
--Grading
--------------------------------------------------------
--functions for calculating grades

exPairToScore :: ((Text,Text),Text) -> Int
exPairToScore ((x,y),z) =  case utcDueDate x of                      
                              Just d -> if asUTC z `laterThan` d       
                                            then 2
                                            else 5
                              Nothing -> 0

scoreById uid = do (a,b,c) <- subsById uid
                   return $ totalScore $ a ++ b ++ c

totalScore xs = foldr (+) 0 (map exPairToScore xs)

--------------------------------------------------------
--Due dates
--------------------------------------------------------
--functions for dealing with time and due dates

asUTC :: Text -> UTCTime
asUTC z = read (unpack z)

toKansasLocal z = ZonedTime (utcToLocalTime centralDaylight z) centralDaylight
    where centralDaylight = TimeZone (-300) False "CDT"

formatted z = formatTime defaultTimeLocale "%l:%M %P %Z, %a %b %e, %Y" (toKansasLocal z)

utcDueDate x = M.lookup (read $ unpack (takeWhile (/= '.') x) :: Int) dueDates

laterThan :: UTCTime -> UTCTime -> Bool
laterThan t1 t2 = diffUTCTime t1 t2 > 0

-- TODO: this should be pushed to a configuration file
-- remember, the day clicks over at midnight.
dueDates :: M.Map Int UTCTime
dueDates = M.fromList [(1, toTime "11:59 pm CDT, Aug 30, 2016")
                      ,(2, toTime "11:30 am CDT, Sep 1, 2016")
                      ,(3, toTime "11:59 pm CDT, Sep 7, 2016")
                      ,(4, toTime "11:59 pm CDT, Sep 7, 2016")
                      ,(5, toTime "11:59 pm CDT, Sep 12, 2016")
                      ,(6, toTime "11:59 pm CDT, Sep 14, 2016")
                      ,(7, toTime "11:59 pm CDT, Sep 19, 2016")
                      ]
    where toTime = parseTimeOrError True defaultTimeLocale "%l:%M %P %Z, %b %e, %Y"

--------------------------------------------------------
--Blaze utility functions
--------------------------------------------------------
--functions for manipulating html

exPairToTable :: [((Text,Text), Text)] -> Html
exPairToTable xs = B.table B.! class_ "table table-striped" $ do
                        B.thead $ do
                            B.th "Exercise"
                            B.th "Content"
                            B.th "Submitted"
                            B.th "Points Earned"
                        B.tbody $ mapM_ toRow xs
        where toRow ((x,y),z) = B.tr $ do B.td $ B.toHtml x
                                          B.td $ B.toHtml (drop 1 y)
                                          B.td $ B.toHtml (formatted $ asUTC z)
                                          B.td $ B.toHtml $ show $ exPairToScore ((x,y),z)

dueDateTable :: Html
dueDateTable = B.table B.! class_ "table table-striped" $ do
                  B.thead $ do
                      B.th "Problem Set"
                      B.th "Due Date"
                  B.tbody $ mapM_ toRow (M.toList dueDates) 
        where toRow (n, d) = B.tr $ do B.td $ B.toHtml $ show n
                                       B.td $ B.toHtml $ formatted d

--------------------------------------------------------
--Database Handling
--------------------------------------------------------
--functions for retrieving database informaiton and formatting it
    
synPair (SyntaxCheckSubmission prob time pu)  = (Just pu, prob,time)

transPair (TranslationSubmission prob time pu)  = (Just pu, prob,time)

derPair (DerivationSubmission prob _ time pu) = (Just pu, prob, time)

subsById uid = do synsubs <- yourSubs synPair uid
                  transsubs <- yourSubs transPair uid
                  dersubs <- yourSubs derPair uid
                  return (synsubs, transsubs, dersubs)

yourSubs pair userId = do subs <- runDB $ selectList [] []
                          let pairs = map (pair . entityVal) subs
                          cpairs <- mapM clean pairs
                          let upairs = filter (\(x,_,_) -> x == userId) cpairs
                          return $ map (\(_,x,y) -> (break (== ':') x ,y)) upairs

clean :: (Maybe (Key User), Text, Text) -> Handler (Text,Text,Text)
clean (Nothing, s,s')  = return ("annonyous", s,s')
clean (Just sid, s,s') = do sub <- runDB $ get404 sid
                            return (userIdent sub, s,s')
