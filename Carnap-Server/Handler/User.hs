module Handler.User where

import Import
import Prelude (read)
import qualified Text.Blaze.Html5 as B
import Text.Blaze.Html5.Attributes
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.GHCJS.SharedTypes
import Data.Aeson (decodeStrict)
import Data.Time
import Util.Data
import Util.Database
import qualified Data.Map as M

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
            UserData firstname lastname enrolledin _ <- checkUserData k
            (synsubs, transsubs,dersubs, ttsubs) <- subsByIdAndSource enrolledin k
            let isAdmin = ident `elem` map instructorEmail instructorsDataList
            assignments <- assignmentsOf enrolledin
            let pointsAvailable = show $ pointsOf (courseData enrolledin)
            derivedRules <- getDrList
            syntable <- problemsToTable enrolledin synsubs
            transtable <- problemsToTable enrolledin transsubs
            dertable <- problemsToTable enrolledin dersubs
            tttable <- problemsToTable enrolledin ttsubs
            score <- totalScore enrolledin synsubs transsubs dersubs ttsubs
            let coursetitle = nameOf (courseData enrolledin)
            defaultLayout $ do
                setTitle "Welcome To Your Homepage!"
                $(widgetFile "user")
    where tryLookup l x = case lookup x l of
                          Just n -> show n
                          Nothing -> "can't find scores"
          
          nouserPage = [whamlet|
                        <div.container>
                            <p> This user does not exist
                       |]

          assignmentsOf theclass = do
             asmd <- runDB $ selectList [AssignmentMetadataCourse ==. theclass] []
             return $
                [whamlet|
                <table.table.table-striped>
                    <thead>
                        <th> Assignment
                        <th> Due Date
                    <tbody>
                        $forall a <- map entityVal asmd
                            <tr>
                                <td>
                                    <a href=@{AssignmentR $ assignmentMetadataFilename a}>
                                        #{assignmentMetadataFilename a}
                                <td>#{show $ assignmentMetadataDuedate a}
                        $maybe dd <- duedates $ courseData theclass
                            $forall (num,date) <- M.toList dd
                                <tr>
                                    <td>
                                        Problem Set #{show num}
                                    <td>
                                        #{formatted date}
                |]

--------------------------------------------------------
--Grading
--------------------------------------------------------
--functions for calculating grades

toScore theclass p = case assignment p of
                   Nothing -> 
                        case utcDueDate theclass (problem p) of                      
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

                            
scoreByIdAndClass theclass uid = 
        do (a,b,c,d) <- subsByIdAndSource theclass uid
           totalScore theclass a b c d

totalScore theclass a b c d = do
           (a',b',c',d') <- (,,,) <$> score a <*> score b <*> score c <*> score d
           return $ a' + b' + c' + d'
   where score :: Problem p => [p] -> Handler Int
         score xs = do xs' <- mapM (toScore theclass) xs
                       return $ foldr (+) 0 xs'

--------------------------------------------------------
--Due dates
--------------------------------------------------------
--functions for dealing with time and due dates

asUTC :: Text -> UTCTime
asUTC z = read (unpack z)

toKansasLocal z = ZonedTime (utcToLocalTime centralDaylight z) centralDaylight
    where centralDaylight = TimeZone (-300) False "CDT"

formatted z = formatTime defaultTimeLocale "%l:%M %P %Z, %a %b %e, %Y" (toKansasLocal z)

utcDueDate theclass x = (duedates $ courseData theclass) >>= M.lookup (read $ unpack (takeWhile (/= '.') x) :: Int) 

laterThan :: UTCTime -> UTCTime -> Bool
laterThan t1 t2 = diffUTCTime t1 t2 > 0


--------------------------------------------------------
--Blaze utility functions
--------------------------------------------------------
--functions for manipulating html

problemsToTable theclass xs = do 
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
        where toRow p = do score <- toScore theclass p 
                           return $ do
                              B.tr $ do B.td $ B.toHtml (takeWhile (/= ':') $ problem p)
                                        B.td $ B.toHtml (drop 1 . dropWhile (/= ':') $ problem p)
                                        B.td $ B.toHtml (formatted $ asUTC $ submitted p )
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

subsByIdAndSource course v = 
        do synsubs   <- runDB $ selectList (queryBy SyntaxCheckSubmissionUserId SyntaxCheckSubmissionSource) []
           transsubs <- runDB $ selectList (queryBy TranslationSubmissionUserId TranslationSubmissionSource) []
           dersubs   <- runDB $ selectList (queryBy DerivationSubmissionUserId DerivationSubmissionSource) []
           ttsubs    <- runDB $ selectList (queryBy TruthTableSubmissionUserId TruthTableSubmissionSource) []
           return (map entityVal synsubs, map entityVal transsubs, map entityVal dersubs, map entityVal ttsubs)
    where queryBy :: EntityField a (Key User) -> EntityField a Util.Data.ProblemSource -> [Filter a]
          queryBy id src = case sourceOf (courseData course) of
               Nothing -> [ id ==. v , src ==. CourseAssignment course] 
               Just c -> [ id ==. v , src ==. CourseAssignment course] ||. [ id ==. v , src ==. c]
