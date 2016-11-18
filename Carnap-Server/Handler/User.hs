module Handler.User where

import Import
import Prelude (read)
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.GHCJS.SharedTypes
import Data.Aeson (decodeStrict)
import Data.Time
import qualified Data.Map as M

deleteUserR :: Text -> Handler Value
deleteUserR userId = do
    msg <- requireJsonBody :: Handler Text
    maybeCurrentUserId <- maybeAuthId
    case maybeCurrentUserId of
        Nothing -> return ()
        Just u -> runDB $ do kl <- selectKeysList [SavedDerivedRuleUserId ==. u
                                                  ,SavedDerivedRuleName ==. msg ] []
                             case kl of
                                 [] -> return ()
                                 (targetkey:_) -> delete targetkey
    returnJson (msg ++ " deleted")

getUserR :: Text -> Handler Html
getUserR userId = do
    (synsubs, transsubs,dersubs, ttsubs) <- subsById userId
    let isAdmin = userId == "gleachkr@gmail.com"
    let pointsAvailable = "725" :: Text
    allUsers <- if isAdmin 
                    then (runDB $ selectList [] []) >>= return . (map $ userIdent . entityVal)
                    else return []
    allScores <- mapM scoreById allUsers >>= return . zip allUsers
    derivedRules <- getDrList
    defaultLayout $ do
        setTitle "Welcome To Your Homepage!"
        $(widgetFile "user")
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

scoreById uid = do (a,b,c,d) <- subsById uid
                   return $ totalScore $ a ++ b ++ c ++ d

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
dueDates = M.fromList [( 1, toTime "11:59 pm CDT, Aug 30, 2016")
                      ,( 2, toTime "11:30 am CDT, Sep 1, 2016")
                      ,( 3, toTime "11:59 pm CDT, Sep 7, 2016")
                      ,( 4, toTime "11:59 pm CDT, Sep 7, 2016")
                      ,( 5, toTime "11:59 pm CDT, Sep 12, 2016")
                      ,( 6, toTime "11:59 pm CDT, Sep 14, 2016")
                      ,( 7, toTime "11:59 pm CDT, Sep 19, 2016")
                      ,( 8, toTime "11:59 pm CDT, Oct 5, 2016")
                      ,( 9, toTime "11:59 pm CDT, Oct 12, 2016")
                      ,(10, toTime "11:59 pm CDT, Oct 12, 2016")
                      ,(11, toTime "11:59 pm CDT, Oct 17, 2016")
                      ,(12, toTime "11:59 pm CDT, Oct 19, 2016")
                      ,(13, toTime "11:59 pm CDT, Oct 24, 2016")
                      ,(14, toTime "11:59 pm CDT, Oct 26, 2016")
                      ,(15, toTime "11:59 pm CDT, Nov 14, 2016")
                      ,(16, toTime "11:59 pm CDT, Nov 18, 2016")
                      ,(17, toTime "11:59 pm CDT, Dec 8, 2016")
                      ]
    where toTime = parseTimeOrError True defaultTimeLocale "%l:%M %P %Z, %b %e, %Y"

--------------------------------------------------------
--Blaze utility functions
--------------------------------------------------------
--functions for manipulating html

exPairToTable :: [((Text,Text), Text)] -> Html
exPairToTable xs = B.table B.! class_ "table table-striped" $ do
                        B.col B.! style "width:50px"
                        B.col B.! style "width:100px"
                        B.col B.! style "width:100px"
                        B.col B.! style "width:100px"
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

formatRules rules = B.table B.! class_ "table table-striped" $ do
        B.thead $ do
            B.th "Name"
            B.th "Premises"
            B.th "Conclusion"
            B.th "Action"
        B.tbody $ mapM_ toRow rules
    where toRow (SavedDerivedRule dr n _ _) = let (Just dr') = decodeStrict dr in 
                                              B.tr $ do B.td $ B.toHtml $ "D-" ++ n
                                                        B.td $ B.toHtml $ intercalate "," $ map show $ premises dr'
                                                        B.td $ B.toHtml $ show $ conclusion dr'
                                                        B.td $ delAct n
          delAct name = B.span B.! class_ "glyphicon glyphicon-trash ruleaction" 
                               B.! onclick (B.textValue $ "tryDeleteRule(\"" ++ name ++ "\")") $ ""

--------------------------------------------------------
--Database Handling
--------------------------------------------------------
--functions for retrieving database infomration and formatting it

getDrList = do maybeCurrentUserId <- maybeAuthId
               case maybeCurrentUserId of
                   Nothing -> return Nothing
                   Just u -> do savedRules <- runDB $ selectList [SavedDerivedRuleUserId ==. u] []
                                return $ Just (formatRules (map entityVal savedRules))
    
synPair (SyntaxCheckSubmission prob time pu)  = (Just pu, prob,time)

transPair (TranslationSubmission prob time pu)  = (Just pu, prob,time)

ttPair  (TruthTableSubmission prob time pu) = (Just pu, prob, time)

derPair (DerivationSubmission prob _ time pu) = (Just pu, prob, time)


subsById uid = do synsubs   <- yourSubs synPair uid
                  transsubs <- yourSubs transPair uid
                  dersubs   <- yourSubs derPair uid
                  ttsubs    <- yourSubs ttPair uid
                  return (synsubs, transsubs, dersubs, ttsubs)

yourSubs pair userId = do subs <- runDB $ selectList [] []
                          -- XXX: It would almost certainly be more
                          -- efficient to do filtering in the query rather
                          -- than after. That makese the code a little less
                          -- generic, but it can probably be fixed.
                          let pairs = map (pair . entityVal) subs
                          cpairs <- mapM clean pairs
                          let upairs = filter (\(x,_,_) -> x == userId) cpairs
                          return $ map (\(_,x,y) -> (break (== ':') x ,y)) upairs

clean :: (Maybe (Key User), Text, Text) -> Handler (Text,Text,Text)
clean (Nothing, s,s')  = return ("annonyous", s,s')
clean (Just sid, s,s') = do sub <- runDB $ get404 sid
                            return (userIdent sub, s,s')
