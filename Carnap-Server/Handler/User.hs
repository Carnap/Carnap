module Handler.User where

import Import
import Prelude (read)
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.GHCJS.SharedTypes
import Data.Aeson (encode, decodeStrict)
import Data.Time
import Util.Data
import Util.Database
import qualified Data.Map as M
import qualified Data.IntMap

deleteUserR :: Text -> Handler Value
deleteUserR ident = do
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
getUserR ident = do
    musr <- runDB $ getBy $ UniqueUser ident
    case musr of 
        Nothing -> defaultLayout nouserPage
        (Just (Entity k _))  -> do
            UserData firstname lastname maybeCourseId maybeInstructorId _ <- checkUserData k
            (synsubs, transsubs,dersubs, ttsubs) <- subsByIdAndSource maybeCourseId k
            let isInstructor = case maybeInstructorId of Just _ -> True; _ -> False
            derivedRules <- getDrList
            utcToKansas' <- liftIO utcToKansas
            case maybeCourseId of
                Just cid ->
                    do Just c <- runDB $ get cid
                       let pointsAvailable = courseTotalPoints c
                           coursetitle = courseTitle c
                       duedates <- getProblemSets cid
                       assignments <- assignmentsOf utcToKansas' cid duedates
                       syntable <- problemsToTable utcToKansas' duedates synsubs
                       transtable <- problemsToTable utcToKansas' duedates transsubs
                       dertable <- problemsToTable utcToKansas' duedates dersubs
                       tttable <- problemsToTable utcToKansas' duedates ttsubs
                       score <- totalScore duedates synsubs transsubs dersubs ttsubs
                       defaultLayout $ do
                           setTitle "Welcome To Your Homepage!"
                           $(widgetFile "user")
                Nothing -> defaultLayout 
                                [whamlet|
                                <div.container>
                                    <p> This user is not enrolled
                                    $if isInstructor
                                        <p> Your instructor page is 
                                            <a href=@{InstructorR ident}>here

                                    <a href=@{AuthR LogoutR}>
                                        Logout
                               |]
    where tryLookup l x = case lookup x l of
                          Just n -> show n
                          Nothing -> "can't find scores"
          
          nouserPage = [whamlet|
                        <div.container>
                            <p> This user does not exist
                       |]


          assignmentsOf localize cid duedates = do
             asmd <- runDB $ selectList [AssignmentMetadataCourse ==. cid] []
             return $
                [whamlet|
                <table.table.table-striped>
                    <thead>
                        <th> Assignment
                        <th> Due Date
                    <tbody>
                        $maybe dd <- duedates
                            $forall (num,date) <- Data.IntMap.toList dd
                                <tr>
                                    <td>
                                        Problem Set #{show num}
                                    <td>
                                        #{formatted localize date}
                        $forall a <- map entityVal asmd
                            <tr>
                                <td>
                                    <a href=@{AssignmentR $ assignmentMetadataFilename a}>
                                        #{assignmentMetadataFilename a}
                                <td>#{formatted localize $ assignmentMetadataDuedate a}
                |]

--------------------------------------------------------
--Grading
--------------------------------------------------------
--functions for calculating grades

toScore duedates p = case assignment p of
                   Nothing -> 
                        case utcDueDate duedates (problem p) of                      
                              Just d -> if asUTC (submitted p) `laterThan` d       
                                            then return (2 :: Int)
                                            else return (5 :: Int)
                              Nothing -> return (0 :: Int)
                   Just a -> do
                        mmd <- runDB $ get a
                        case mmd of
                            Nothing -> return (0 :: Int)
                            Just v -> do
                                if asUTC (submitted p) `laterThan` assignmentMetadataDuedate v
                                    then return (2 :: Int)
                                    else return (5 :: Int)

                            
scoreByIdAndClass cid uid = 
        do (a,b,c,d) <- subsByIdAndSource (Just cid) uid
           duedates <-  getProblemSets cid
           totalScore duedates a b c d

totalScore duedates a b c d = do
           (a',b',c',d') <- (,,,) <$> score a <*> score b <*> score c <*> score d
           return $ a' + b' + c' + d'
   where score :: Problem p => [p] -> Handler Int
         score xs = do xs' <- mapM (toScore duedates) xs
                       return $ foldr (+) 0 xs'

--------------------------------------------------------
--Due dates
--------------------------------------------------------
--functions for dealing with time and due dates

asUTC :: Text -> UTCTime
asUTC z = read (unpack z)

utcToKansas = do nyctz <- getCurrentTimeZone 
                 --XXX: Server is in NYC. Do this dynamically to handle daylight savings, etc.
                 let kstz = TimeZone (timeZoneMinutes nyctz - 60) False "CDT"
                 return (\z -> ZonedTime (utcToLocalTime kstz z) kstz)

formatted localize z = formatTime defaultTimeLocale "%l:%M %P %Z, %a %b %e, %Y" (localize z)

utcDueDate duedates x = duedates >>= Data.IntMap.lookup (read $ unpack (takeWhile (/= '.') x) :: Int) 

laterThan :: UTCTime -> UTCTime -> Bool
laterThan t1 t2 = diffUTCTime t1 t2 > 0


--------------------------------------------------------
--Blaze utility functions
--------------------------------------------------------
--functions for manipulating html

problemsToTable localize duedates xs = do 
            rows <- mapM toRow xs
            return $ do B.table B.! class_ "table table-striped" $ do
                            B.col B.! style "width:50px"
                            B.col B.! style "width:100px"
                            B.col B.! style "width:100px"
                            B.col B.! style "width:100px"
                            B.thead $ do
                                B.th "Exercise"
                                B.th "Content"
                                B.th "Submitted"
                                B.th "Points Earned"
                            B.tbody $ sequence_ rows
        where toRow p = do score <- toScore duedates p 
                           return $ do
                              B.tr $ do B.td $ B.toHtml (takeWhile (/= ':') $ problem p)
                                        B.td $ B.toHtml (drop 1 . dropWhile (/= ':') $ problem p)
                                        B.td $ B.toHtml (formatted localize $ asUTC $ submitted p )
                                        B.td $ B.toHtml $ show $ score

tryDelete name = "tryDeleteRule(\"" <> name <> "\")"

--------------------------------------------------------
--Database Handling
--------------------------------------------------------
--functions for retrieving database infomration and formatting it

getDrList = do maybeCurrentUserId <- maybeAuthId
               case maybeCurrentUserId of
                   Nothing -> return Nothing
                   Just u -> do savedRules <- runDB $ selectList 
                                    [SavedDerivedRuleUserId ==. u] []
                                case savedRules of 
                                    [] -> return Nothing
                                    _  -> return $ Just (map entityVal savedRules)

class Problem p where
        problem :: p -> Text
        submitted :: p -> Text
        assignment :: p -> Maybe AssignmentMetadataId

instance Problem SyntaxCheckSubmission where
        problem (SyntaxCheckSubmission prob _ _ _ _) = prob
        submitted (SyntaxCheckSubmission _ time _ _ _) = time
        assignment (SyntaxCheckSubmission _ _ _ _ key) = key

instance Problem TranslationSubmission where
        problem (TranslationSubmission prob _ _ _ _) = prob
        submitted (TranslationSubmission _ time _ _ _) = time
        assignment (TranslationSubmission _ _ _ _ key) = key

instance Problem TruthTableSubmission where
        problem (TruthTableSubmission prob _ _ _ _) = prob
        submitted (TruthTableSubmission _ time _ _ _) = time
        assignment (TruthTableSubmission _ _ _ _ key) = key

instance Problem DerivationSubmission where
        problem (DerivationSubmission prob _ _ _ _ _) = prob
        submitted (DerivationSubmission _ _ time _ _ _) = time
        assignment (DerivationSubmission _ _ _ _ _ key) = key

subsByIdAndSource Nothing _ = return ([],[],[],[])
subsByIdAndSource (Just cid) v = 
        do synsubs   <- runDB $ selectList (queryBy SyntaxCheckSubmissionUserId SyntaxCheckSubmissionSource) []
           transsubs <- runDB $ selectList (queryBy TranslationSubmissionUserId TranslationSubmissionSource) []
           dersubs   <- runDB $ selectList (queryBy DerivationSubmissionUserId DerivationSubmissionSource) []
           ttsubs    <- runDB $ selectList (queryBy TruthTableSubmissionUserId TruthTableSubmissionSource) []
           return (map entityVal synsubs, map entityVal transsubs, map entityVal dersubs, map entityVal ttsubs)
    where queryBy :: EntityField a (Key User) -> EntityField a ByteString -> [Filter a]
          queryBy id src = [ id ==. v , src ==. (toStrict . encode) (CourseAssignment cid) ] ||. [ id ==. v , src ==. (toStrict . encode) (CarnapTextbook)]
