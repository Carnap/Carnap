{-#LANGUAGE DeriveGeneric, OverloadedStrings#-}
module Carnap.GHCJS.SharedTypes (
        GHCJSCommand(..), ProblemSource(..)
) where

import Prelude
import Data.Aeson
import Data.Either
import Text.Parsec (parse)
import GHC.Generics
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.Languages.PurePropositional.Parser

data ProblemSource = Book
                   | BirminghamAssignment
        deriving (Generic, Show, Read, Eq)

instance ToJSON ProblemSource

instance FromJSON ProblemSource

--XXX: these should be more structured.
data GHCJSCommand = EchoBack (String, Bool)
        | SubmitSyntaxCheck String ProblemSource
        | SubmitTranslation String ProblemSource
        | SubmitDerivation String String ProblemSource
        | SubmitTruthTable String ProblemSource
        | SaveDerivedRule String DerivedRule
        | RequestDerivedRulesForUser
        deriving (Generic, Show)

instance ToJSON GHCJSCommand

instance FromJSON GHCJSCommand

instance ToJSON DerivedRule where
        toJSON (DerivedRule conclusion prems) = 
            object [ "conclusion" .= show conclusion
                   , "premises"   .= map show prems]

instance FromJSON DerivedRule where
        parseJSON (Object v) = 
            do c  <- v .: "conclusion"
               ps <- v .: "premises"
               let ps' = map toForm ps 
               case (toForm c, lefts ps') of 
                 (Right f, []) -> return $ DerivedRule f (rights ps')
                 _ -> mempty
            where toForm = parse (purePropFormulaParser "PQRSTUVW") ""
        parseJSON _ = mempty
