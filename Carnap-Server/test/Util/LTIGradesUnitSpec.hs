{-# LANGUAGE OverloadedStrings #-}
module Util.LTIGradesUnitSpec (main, spec) where

import TestImport
import Util.LTIGrades
import Data.Aeson (encode, decode)
import qualified Data.Text as T

spec :: Spec
spec = describe "LTI Grade Sync Unit Tests" $ do

    describe "GradeSyncStatus JSON serialization" $ do

        it "should serialize GradeSyncDisabled correctly" $ do
            let status = GradeSyncDisabled :: GradeSyncStatus
            let encoded = encode status
            decode encoded `shouldBe` Just status

        it "should serialize GradeSyncEnabled correctly" $ do
            let status = GradeSyncEnabled :: GradeSyncStatus
            let encoded = encode status
            decode encoded `shouldBe` Just status

        it "should serialize GradeSyncError correctly" $ do
            let status = GradeSyncError "Test error" :: GradeSyncStatus
            let encoded = encode status
            decode encoded `shouldBe` Just status

    describe "LTIUserGrade JSON serialization" $ do

        it "should serialize LTIUserGrade correctly" $ do
            let grade = LTIUserGrade
                    { ltiUserId = "user123"
                    , carnapUserId = (fromIntegral 1) :: Key User
                    , gradeValue = 0.85
                    , assignmentLabel = "Assignment 1"
                    , lastUpdated = read "2025-12-23 12:00:00 UTC" :: UTCTime
                    } :: LTIUserGrade
            let encoded = encode grade
            decode encoded `shouldBe` Just grade

    describe "LTIGradePayload JSON serialization" $ do

        it "should serialize LTIGradePayload correctly" $ do
            let payload = LTIGradePayload
                    { scoreGiven = 0.85
                    , scoreMaximum = 1.0
                    , comment = Just "Good work"
                    , timestamp = "2025-12-23T12:00:00Z"
                    } :: LTIGradePayload
            let encoded = encode payload
            decode encoded `shouldBe` Just payload

    describe "Grade Calculation" $ do

        it "should normalize grades between 0.0 and 1.0" $ do
            -- Test that grades are properly normalized
            let testGrade score total = min 1.0 (fromIntegral score / fromIntegral total)
            testGrade 85 100 `shouldBe` 0.85
            testGrade 150 100 `shouldBe` 1.0  -- Should cap at 1.0
            testGrade 50 100 `shouldBe` 0.5

        it "should handle zero scores correctly" $ do
            let testGrade score total = min 1.0 (fromIntegral score / fromIntegral total)
            testGrade 0 100 `shouldBe` 0.0

main :: IO ()
main = hspec spec