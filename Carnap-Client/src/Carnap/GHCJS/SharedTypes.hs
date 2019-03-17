{-#LANGUAGE DeriveGeneric, StandaloneDeriving, FlexibleContexts, UndecidableInstances, FlexibleInstances, OverloadedStrings#-}
module Carnap.GHCJS.SharedTypes (
    GHCJSCommand(..), ProblemSource(..), ProblemType(..), ProblemData(..), DerivedRule(..), PropDerivedRule, derivedRuleToSequent, decodeRule
) where

import Prelude
import Data.Aeson (ToJSON(..), FromJSON(..), Value(..), object, (.=), (.:), decodeStrict)
import Text.Read
import Data.Text (Text)
import Data.ByteString (ByteString)
import Text.Parsec (parse, eof)
import GHC.Generics
import Carnap.Core.Data.Types (FixLang, Form)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser

data ProblemSource = Book | Assignment String
        deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemSource

instance FromJSON ProblemSource

data ProblemType = Derivation | TruthTable | Translation | SyntaxCheck
    deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemType

instance FromJSON ProblemType

type TruthTable = [[Maybe Bool]]

type Options = [(String,String)]

data ProblemData = DerivationData Text Text 
                 | DerivationDataOpts Text Text Options
                 | TruthTableData Text TruthTable
                 | TruthTableDataOpts Text TruthTable Options
                 | TranslationData Text Text
                 | TranslationDataOpts Text Text Options
                 | ProblemContent Text
    deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemData

instance FromJSON ProblemData

data DerivedRule lex sem = DerivedRule { conclusion :: FixLang lex sem, premises :: [FixLang lex sem]}
deriving instance Show (FixLang lex sem) => Show (DerivedRule lex sem)
deriving instance Eq (FixLang lex sem) => Eq (DerivedRule lex sem)

derivedRuleToSequent (DerivedRule c ps) = antecedent :|-: SS (liftToSequent c)
    where antecedent = foldr (:+:) Top (map (SA . liftToSequent) ps)

--XXX: these should be more structured.
data GHCJSCommand = EchoBack (String, Bool)
        | Submit ProblemType String ProblemData ProblemSource Bool (Maybe Int) String 
        | SaveDerivedRule String (DerivedRule PurePropLexicon (Form Bool))
        | RequestDerivedRulesForUser
        deriving (Generic, Show)

instance ToJSON GHCJSCommand

instance FromJSON GHCJSCommand

instance Show (FixLang lex sem) => ToJSON (DerivedRule lex sem) where
        toJSON (DerivedRule conclusion prems) = 
            object [ "conclusion" .= show conclusion
                   , "premises"   .= map show prems]

type PropDerivedRule = DerivedRule PurePropLexicon (Form Bool)

instance Read (FixLang lex sem) => FromJSON (DerivedRule lex sem) where
        parseJSON (Object v) = 
            do c  <- v .: "conclusion"
               ps <- v .: "premises"
               let ps' = mapM toForm ps 
               case (toForm c, ps') of 
                 (Just f, Just ps'') -> return $ DerivedRule f ps''
                 _ -> mempty
            where toForm x = readMaybe x
        parseJSON _ = mempty

decodeRule :: ByteString -> Maybe PropDerivedRule
decodeRule = decodeStrict 
