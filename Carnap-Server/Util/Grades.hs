{-#LANGUAGE DeriveGeneric #-}
module Util.Grades where

import Import
import Util.Data
import Util.Database
import Data.Time
import Data.Monoid
import Data.Time.Zones
import Data.Time.Zones.DB
import Data.Time.Zones.All
import qualified Data.IntMap as IM
import Text.Read (read, readMaybe)

--This is probably marginally more efficient when you have problems but not
--a list of assignments
toScore :: Key User -> Int -> Maybe BookAssignmentTable -> ProblemSubmission -> HandlerFor App Int
toScore uid accommodation textbookproblems p = 
        case (problemSubmissionAssignmentId p, problemSubmissionCorrect p) of
               (_,False) -> return extra
               (Nothing,True) -> return $
                    case ( utcDueDate textbookproblems (problemSubmissionIdent p)
                         , problemSubmissionCredit p) of
                          (Just d, Just c) ->  theGrade d accommodation c p + extra
                          (Just d, Nothing) ->  theGrade d accommodation 5 p + extra
                          (Nothing,_) -> 0
               (Just a,True) -> do
                    (mmd,mex) <- runDB $ (,) <$> get a <*> getBy (UniqueExtension a uid)
                    case mmd of
                        Nothing -> return 0
                        Just v -> return $
                            case ( (extensionUntil . entityVal <$> mex) <|> assignmentMetadataDuedate v 
                                 , problemSubmissionCredit p) of
                                    (Just d, Just c) -> theGrade d accommodation c p + extra
                                    (Just d, Nothing) -> theGrade d accommodation 5 p + extra
                                    (Nothing, Just c) -> c + extra
                                    (Nothing, Nothing) -> 5 + extra
    where extra = maybe 0 id $ problemSubmissionExtra p
          
--This is probably marginally more efficient when you have already looked
--up a list of assignments from the DB.
toScoreAny :: Maybe BookAssignmentTable -> [(Entity AssignmentMetadata, Maybe (Entity Extension))] -> Int -> ProblemSubmission 
    -> Int
toScoreAny textbookproblems asgns accommodation p = maybe 0 id (getAlt $ mconcat $ tbscore : asgnscores)
    where tbscore = Alt $ toScoreBook textbookproblems accommodation p
          asgnscores = map (\(asgn, mex) -> Alt $ toScoreByAssignment asgn mex accommodation p) asgns

toScoreBook :: Maybe BookAssignmentTable -> Int -> ProblemSubmission -> Maybe Int
toScoreBook textbookproblems accommodation p = 
        case (problemSubmissionAssignmentId p, problemSubmissionCorrect p) of
               (_,False) -> Just $ extra
               (Nothing,True) -> Just $
                    case ( utcDueDate textbookproblems (problemSubmissionIdent p)
                         , problemSubmissionCredit p) of
                          (Just d, Just c) ->  theGrade d accommodation c p + extra
                          (Just d, Nothing) ->  theGrade d accommodation 5 p + extra
                          (Nothing,_) -> 0
               _ -> Nothing
    where extra = maybe 0 id $ problemSubmissionExtra p

toScoreByAssignment :: Entity AssignmentMetadata -> Maybe (Entity Extension) -> Int -> ProblemSubmission -> Maybe Int
toScoreByAssignment (Entity asgnk asgn) mex accommodation p = 
        case (problemSubmissionAssignmentId p, problemSubmissionCorrect p) of
               (_,False) -> Just $ extra
               (Just a,True) | a == asgnk -> Just $
                    case ( (extensionUntil . entityVal <$> mex) <|> assignmentMetadataDuedate asgn 
                         , problemSubmissionCredit p) of
                        (Just d, Just c) -> theGrade d accommodation c p + extra
                        (Just d, Nothing) -> theGrade d accommodation 5 p + extra
                        (Nothing, Just c) -> c + extra
                        (Nothing, Nothing) -> 5 + extra
               _ -> Nothing
    where extra = maybe 0 id $ problemSubmissionExtra p

theGrade :: UTCTime -> Int -> Int -> ProblemSubmission -> Int
theGrade due accommodation points p' = case problemSubmissionLateCredit p' of
      Nothing | problemSubmissionTime p' `laterThan` (accommodationUTC `addUTCTime` due) -> floor ((fromIntegral points :: Rational) / 2)
      Just n  | problemSubmissionTime p' `laterThan` (accommodationUTC `addUTCTime` due) -> n
      _ -> points
    where accommodationUTC = fromIntegral (3600 * accommodation) :: NominalDiffTime

scoreByIdAndClassTotal :: Key Course -> Key User -> HandlerFor App Int
scoreByIdAndClassTotal cid uid =
        do perprob <- scoreByIdAndClassPerProblem cid uid
           return $ foldr (+) 0 (map (\(_,y,_) -> y) perprob)

scoreByIdAndClassPerProblem :: Key Course -> Key User -> HandlerFor App [(Either (Key AssignmentMetadata) Text, Int, Text)]
scoreByIdAndClassPerProblem cid uid =
        do pq <- getProblemQuery uid cid
           subs <- map entityVal <$> (runDB $ selectList pq [])
           textbookproblems <- getProblemSets cid
           accommodation <- (runDB $ getBy $ UniqueAccommodation cid uid) 
                        >>= return . maybe 0 (accommodationDateExtraHours . entityVal)
           scoreList uid accommodation textbookproblems subs

scoreList :: Traversable t => Key User -> Int -> Maybe BookAssignmentTable -> t ProblemSubmission 
    -> HandlerFor App (t (Either (Key AssignmentMetadata) Text, Int, Text))
scoreList uid accommodation textbookproblems = mapM (\x -> do score <- toScore uid accommodation textbookproblems x
                                                              return (getLabel x, score, problemSubmissionIdent x))
   where getLabel x = case problemSubmissionAssignmentId x of
                          --get assignment metadata id
                          Just amid -> Left amid
                          --otherwise, must be a textbook problem
                          Nothing -> Right $ takeWhile (/= '.') (problemSubmissionIdent x)

utcDueDate :: (IsSequence t, Element t ~ Char) => Maybe BookAssignmentTable -> t -> Maybe UTCTime
utcDueDate textbookproblems x = textbookproblems >>= IM.lookup theIndex . readAssignmentTable
    where theIndex = read . unpack . takeWhile (/= '.') $ x :: Int
