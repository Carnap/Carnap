{-#LANGUAGE DeriveGeneric, OverloadedStrings#-}
module Carnap.GHCJS.SharedTypes (
        GHCJSCommand(..), ProblemSource(..), ProblemType(..), ProblemData(..)
) where

import Prelude
import Data.Aeson
import Data.Either
import Data.Text (Text)
import Text.Parsec (parse, eof)
import GHC.Generics
import Carnap.Languages.PurePropositional.Logic (DerivedRule(..))
import Carnap.Languages.PurePropositional.Parser

data ProblemSource = Book | Assignment String
        deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemSource

instance FromJSON ProblemSource

data ProblemType = Derivation | TruthTable | Translation | SyntaxCheck
    deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemType

instance FromJSON ProblemType

data ProblemData = DerivationData Text Text | ProblemContent Text
    deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemData

instance FromJSON ProblemData

--XXX: these should be more structured.
data GHCJSCommand = EchoBack (String, Bool)
        | Submit ProblemType String ProblemData ProblemSource String
        | SubmitSyntaxCheck String ProblemSource String
        | SubmitTranslation String ProblemSource String
        | SubmitDerivation String String ProblemSource String
        | SubmitTruthTable String ProblemSource String
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
            where toForm = parse (purePropFormulaParser standardLetters <* eof) ""
        parseJSON _ = mempty
