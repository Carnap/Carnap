module Handler.User where

import Import
import Prelude (read)
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Data.Time
import qualified Data.Map as M

getUserR :: Text -> Handler Html
getUserR userId = do
    synsubs <- yourSubs synPair userId
    transsubs <- yourSubs transPair userId
    defaultLayout $ do
        setTitle "Welcome To Your Homepage!"
        [whamlet|
            <div.container>
                <h1> Homepage for #{userId}
                <p> This is your homepage, where you can keep track of your progress in the course, and find other useful information.
                <h3 style="padding-top:10pt"> Completed Problems
                <h4> Syntax Checking
                #{exPairToTable synsubs}
                <h4> Translation
                #{exPairToTable transsubs}
                <div.row>
                    <div.col-md-9 style="padding-right:30pt">
                        <h3> Due Dates
                        #{dueDateTable}
                    <div.col-md-3>
                        <h3> Total Points Earned
                        <span style="font-size:56pt; color:gray; padding-left:20pt"> #{totalScore (synsubs ++ transsubs)}/50
                <div>
                <a href=@{AuthR LogoutR}>
                    Logout
        |]

textToUl :: [Text] -> Html
textToUl xs = do B.ul $ mapM_ (B.li . B.toHtml) xs

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

totalScore xs = foldr (+) 0 (map exPairToScore xs)

exPairToScore :: ((Text,Text),Text) -> Int
exPairToScore ((x,y),z) =  case utcDueDate x of                      
                              Just d -> if asUTC z `laterThan` d       
                                            then 0
                                            else 5
                              Nothing -> 0

asUTC :: Text -> UTCTime
asUTC z = read (unpack z)

centralDaylight = TimeZone (-300) False "CDT"

toKansasLocal z = ZonedTime (utcToLocalTime centralDaylight z) centralDaylight

formatted z = formatTime defaultTimeLocale "%l:%M %P %Z, %a %b %e, %Y" (toKansasLocal z)

utcDueDate x = M.lookup (read $ unpack (takeWhile (/= '.') x) :: Int) dueDates

printDueDate x = case utcDueDate x of
                Just d -> formatted d
                Nothing -> "None"

dueDateTable :: Html
dueDateTable = B.table B.! class_ "table table-striped" $ do
                  B.thead $ do
                      B.th "Problem Set"
                      B.th "Due Date"
                  B.tbody $ mapM_ toRow (M.toList dueDates) 
        where toRow (n, d) = B.tr $ do B.td $ B.toHtml $ show n
                                       B.td $ B.toHtml $ formatted d

laterThan :: UTCTime -> UTCTime -> Bool
laterThan t1 t2 = diffUTCTime t1 t2 > 0

-- TODO: this should be pushed to a configuration file
-- remember, the day clicks over at midnight.
dueDates :: M.Map Int UTCTime
dueDates = M.fromList [(1, toTime "12:00 am CDT, Aug 30, 2016")
                      ]
    where toTime = parseTimeOrError True defaultTimeLocale "%l:%M %P %Z, %b %e, %Y"

yourSubs pair userId = do subs <- runDB $ selectList [] []
                          let pairs = map (pair . fromEnt) subs
                          cpairs <- mapM clean pairs
                          let upairs = filter (\(x,_,_) -> x == userId) cpairs
                          return $ map (\(_,x,y) -> (break (== ':') x ,y)) upairs
    
synPair (SyntaxCheckSubmission prob time pu)  = (Just pu, prob,time)

transPair (TranslationSubmission prob time pu)  = (Just pu, prob,time)

clean :: (Maybe (Key User), Text, Text) -> Handler (Text,Text,Text)
clean (Nothing, s,s')  = return ("annonyous", s,s')
clean (Just sid, s,s') = do sub <- runDB $ get404 sid
                            return (userIdent sub, s,s')

fromEnt (Entity k v) = v
