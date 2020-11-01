{-#LANGUAGE DeriveGeneric #-}
module Util.Grades where

import Import
import Util.Data
import Util.Database
import Data.Time
import Data.Time.Zones
import Data.Time.Zones.DB
import Data.Time.Zones.All
import qualified Data.IntMap as IM
import Text.Read (read, readMaybe)

toScore
    :: Int
    -> Maybe BookAssignmentTable
    -> ProblemSubmission
    -> HandlerFor App Int
toScore extension textbookproblems p = 
        case (problemSubmissionAssignmentId p, problemSubmissionCorrect p) of
               (_,False) -> return extra
               (Nothing,True) -> return $
                    case ( utcDueDate textbookproblems (problemSubmissionIdent p)
                         , problemSubmissionCredit p) of
                          (Just d, Just c) ->  theGrade d c p + extra
                          (Just d, Nothing) ->  theGrade d 5 p + extra
                          (Nothing,_) -> 0
               (Just a,True) -> do
                    mmd <- runDB $ get a
                    case mmd of
                        Nothing -> return 0
                        Just v -> return $
                            case ( assignmentMetadataDuedate v
                                 , problemSubmissionCredit p) of
                                    (Just d, Just c) -> theGrade d c p + extra
                                    (Just d, Nothing) -> theGrade d 5 p + extra
                                    (Nothing, Just c) -> c + extra
                                    (Nothing, Nothing) -> 5 + extra
    where extra = case problemSubmissionExtra p of Nothing -> 0; Just e -> e
          extensionUTC = fromIntegral (3600 * extension) :: NominalDiffTime
          theGrade :: UTCTime -> Int -> ProblemSubmission -> Int
          theGrade due points p' = 
            case problemSubmissionLateCredit p' of
                  Nothing | problemSubmissionTime p' `laterThan` (extensionUTC `addUTCTime` due) -> floor ((fromIntegral points :: Rational) / 2)
                  Just n  | problemSubmissionTime p' `laterThan` (extensionUTC `addUTCTime` due) -> n
                  _ -> points

scoreByIdAndClassTotal :: Key Course -> Key User -> HandlerFor App Int
scoreByIdAndClassTotal cid uid =
        do perprob <- scoreByIdAndClassPerProblem cid uid
           return $ foldr (+) 0 (map (\(_,y,_) -> y) perprob)

scoreByIdAndClassPerProblem :: Key Course -> Key User -> HandlerFor App [(Either (Key AssignmentMetadata) Text, Int, Text)]
scoreByIdAndClassPerProblem cid uid =
        do pq <- getProblemQuery uid cid
           subs <- map entityVal <$> (runDB $ selectList pq [])
           textbookproblems <- getProblemSets cid
           extension <- (runDB $ getBy $ UniqueAccommodation cid uid) 
                        >>= return . maybe 0 (accommodationDateExtraHours . entityVal)
           scoreList extension textbookproblems subs

totalScore :: (Traversable t, MonoFoldable (t Int), Num (Element (t Int))) => 
    Int -> Maybe BookAssignmentTable -> t ProblemSubmission -> HandlerFor App (Element (t Int))
totalScore extension textbookproblems xs =
        do xs' <- mapM (toScore extension textbookproblems) xs
           return $ foldr (+) 0 xs'

scoreList :: Traversable t => Int -> Maybe BookAssignmentTable -> t ProblemSubmission 
    -> HandlerFor App (t (Either (Key AssignmentMetadata) Text, Int, Text))
scoreList extension textbookproblems = mapM (\x -> do score <- toScore extension textbookproblems x
                                                      return (getLabel x, score, problemSubmissionIdent x))
   where getLabel x = case problemSubmissionAssignmentId x of
                          --get assignment metadata id
                          Just amid -> Left amid
                          --otherwise, must be a textbook problem
                          Nothing -> Right $ takeWhile (/= '.') (problemSubmissionIdent x)

utcDueDate :: (IsSequence t, Element t ~ Char) => Maybe BookAssignmentTable -> t -> Maybe UTCTime
utcDueDate textbookproblems x = textbookproblems >>= IM.lookup theIndex . readAssignmentTable
    where theIndex = read . unpack . takeWhile (/= '.') $ x :: Int
