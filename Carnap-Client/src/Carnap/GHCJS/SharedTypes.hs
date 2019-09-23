{-#LANGUAGE DeriveGeneric, StandaloneDeriving, FlexibleContexts, UndecidableInstances, FlexibleInstances, OverloadedStrings#-}
module Carnap.GHCJS.SharedTypes (
    GHCJSCommand(..), ProblemSource(..), ProblemType(..), ProblemData(..), DerivedRule(..)
    , derivedRuleToSequent, decodeRule, SomeRule(..), inspectPrems, inspectConclusion
) where

import Prelude
import Data.Aeson (ToJSON(..), FromJSON(..), Value(..), object, (.=), (.:), decodeStrict)
import Data.Tree (Tree)
import Text.Read
import Data.Text (Text)
import Data.ByteString (ByteString)
import Text.Parsec (parse, eof)
import GHC.Generics
import Carnap.Core.Data.Types (FixLang, Form)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PureFirstOrder.Parser

data ProblemSource = Book | Assignment String
        deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemSource

instance FromJSON ProblemSource

data ProblemType = Derivation | TruthTable | Translation | SyntaxCheck | CounterModel | Qualitative | SequentCalc
    deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemType

instance FromJSON ProblemType

type TruthTable = [[Maybe Bool]]

type Options = [(String,String)]

type CounterModelFields = [(String,String)]

data ProblemData = DerivationData Text Text 
                 | DerivationDataOpts Text Text Options
                 | SequentCalcData Text (Tree (String,String)) Options
                 | TruthTableData Text TruthTable
                 | TruthTableDataOpts Text TruthTable Options
                 | TranslationData Text Text
                 | TranslationDataOpts Text Text Options
                 | CounterModelDataOpts Text CounterModelFields Options
                 | QualitativeProblemDataOpts Text Text Options
                 | ProblemContent Text
    deriving (Show, Read, Eq, Generic)

instance ToJSON ProblemData

instance FromJSON ProblemData

data DerivedRule lex sem = DerivedRule { conclusion :: FixLang lex sem, premises :: [FixLang lex sem] }
deriving instance Show (FixLang lex sem) => Show (DerivedRule lex sem)
deriving instance Read (FixLang lex sem) => Read (DerivedRule lex sem)
deriving instance Eq (FixLang lex sem) => Eq (DerivedRule lex sem)

derivedRuleToSequent (DerivedRule c ps) = antecedent :|-: SS (liftToSequent c)
    where antecedent = foldr (:+:) Top (map (SA . liftToSequent) ps)

data GHCJSCommand = Submit ProblemType String ProblemData ProblemSource Bool (Maybe Int) String 
                  | SaveRule String SomeRule
                  | RequestDerivedRulesForUser
        deriving (Generic, Show)

instance ToJSON GHCJSCommand

instance FromJSON GHCJSCommand

instance Show (FixLang lex sem) => ToJSON (DerivedRule lex sem) where
        toJSON (DerivedRule conclusion prems) = 
            object [ "conclusion" .= show conclusion
                   , "premises"   .= map show prems
                   ]

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

decodeRule :: ByteString -> Maybe (DerivedRule PurePropLexicon (Form Bool))
decodeRule = decodeStrict 

--naming convention: _Rule is assocated with _Calc
data SomeRule = PropRule (DerivedRule PurePropLexicon (Form Bool))
              | FOLRule (DerivedRule PureLexiconFOL (Form Bool))
    deriving (Show, Read, Eq, Generic)

inspectPrems (PropRule r) = map show $ premises r
inspectPrems (FOLRule r) = map show $ premises r

inspectConclusion (PropRule r) = show $ conclusion r
inspectConclusion (FOLRule r) = show $ conclusion r

instance ToJSON SomeRule

instance FromJSON SomeRule
