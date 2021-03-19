{-#LANGUAGE ConstraintKinds, RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gentzen
( parseGentzenFOLK, gentzenFOLKCalc, GentzenFOLK(..)
, parseGentzenFOLJ, gentzenFOLJCalc, GentzenFOLJ(..)
) where

import Text.Parsec
import Data.List
import Data.Typeable
import Control.Lens
import Control.Monad
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Core.Data.Types
import Carnap.Core.Unification.Unification
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Gentzen
import Carnap.Languages.Util.GenericConstructors
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.Util
import Carnap.Languages.Util.LanguageClasses

data GentzenFOLK = LK GentzenPropLK 
                | AllL   | AllR
                | ExistL | ExistR

newtype GentzenFOLJ = LJ GentzenFOLK

instance Show GentzenFOLK where
    show (LK x) = show x
    show AllL   = "∀L"
    show AllR   = "∀R"
    show ExistL = "∃L"
    show ExistR = "∃R"

instance Show GentzenFOLJ where
    show (LJ x) = show x

parseGentzenFOLK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [GentzenFOLK]
parseGentzenFOLK rtc = try folParse <|> liftProp
        where liftProp = map LK <$> parseGentzenPropLK rtc
              folParse = do r <- choice (map (try . string) [ "AL", "∀L", "AR","∀R", "EL","∃L", "ER", "∃R" ])
                            return $ (\x -> [x]) $ case r of
                               r | r `elem` ["AL","∀L"] -> AllL
                                 | r `elem` ["AR","∀R"] -> AllR
                                 | r `elem` ["EL","∃L"] -> ExistL
                                 | r `elem` ["ER","∃R"] -> ExistR

parseGentzenFOLJ :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [GentzenFOLJ]
parseGentzenFOLJ rtc = map LJ <$> parseGentzenFOLK rtc

type LKAdequate lex = ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemeConstantLanguage (ClassicalSequentOver lex (Term Int))
         , QuantLanguage (ClassicalSequentOver lex (Form Bool)) (ClassicalSequentOver lex (Term Int)) 
         , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form Bool)
         , PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) Int Int 
         , PrismIndexedConstant (ClassicalSequentLexOver lex) Int
         , PrismStandardVar (ClassicalSequentLexOver lex) Int
         , CopulaSchema (ClassicalSequentOver lex)
         , Eq (ClassicalSequentOver lex (Form Bool))
         , Schematizable (lex (ClassicalSequentOver lex))
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , PrismSubstitutionalVariable (ClassicalSequentLexOver lex)
         )

instance LKAdequate lex => CoreInference GentzenFOLK lex (Form Bool) where
         corePremisesOf (LK x) = corePremisesOf x
         corePremisesOf AllL = [SA (phi 1 (taun 1)) :+: GammaV 1 :|-: DeltaV 1]
         corePremisesOf AllR = [ GammaV 1 :|-: DeltaV 1 :-: SS (phi 1 (taun 1))]
         corePremisesOf ExistL = [SA (phi 1 (taun 1)) :+: GammaV 1 :|-: DeltaV 1]
         corePremisesOf ExistR = [ GammaV 1 :|-: DeltaV 1 :-: SS (phi 1 (taun 1))]

         coreConclusionOf (LK x) = coreConclusionOf x
         coreConclusionOf AllL = SA (lall "v" (phi 1)) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf AllR =  GammaV 1 :|-: DeltaV 1 :-: SS (lall "v" (phi 1))
         coreConclusionOf ExistL = SA (lsome "v" (phi 1)) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf ExistR =  GammaV 1 :|-: DeltaV 1 :-: SS (lsome "v" (phi 1))

         coreRestriction AllR = Just $ eigenConstraint (taun 1) (SS (lall "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction ExistL = Just $ eigenConstraint (taun 1) (fodelta 1) (SA (lsome "v" (phi' 1)) :+: fogamma 1)
         coreRestriction _ = Nothing

instance SpecifiedUnificationType GentzenFOLK

instance LKAdequate lex => CoreInference GentzenFOLJ lex (Form Bool) where
         corePremisesOf (LJ x) = corePremisesOf x

         coreConclusionOf (LJ x) = coreConclusionOf x

         coreRestriction (LJ x) = case coreRestriction x of
                                      Nothing -> Just $ \sub -> monoConsequent (applySub sub $ coreConclusionOf x)
                                      Just f -> Just $ \sub -> f sub `mplus` monoConsequent (applySub sub $ coreConclusionOf x)
             where monoConsequent :: forall lex . Eq (ClassicalSequentOver lex (Form Bool)) => ClassicalSequentOver lex (Sequent (Form Bool)) -> Maybe String
                   monoConsequent (_:|-:x)= case nub (toListOf concretes x :: [ClassicalSequentOver lex (Form Bool)]) of
                                              _:_:xs -> Just "LJ requires that the right hand side of each sequent contain at most one formula"
                                              _ -> Nothing

instance SpecifiedUnificationType GentzenFOLJ

gentzenFOLKCalc :: TableauCalc PureLexiconFOL (Form Bool) GentzenFOLK
gentzenFOLKCalc = mkTBCalc
    { tbParseForm = langParser
    , tbParseRule = parseGentzenFOLK
    }

gentzenFOLJCalc :: TableauCalc PureLexiconFOL (Form Bool) GentzenFOLJ
gentzenFOLJCalc = mkTBCalc
    { tbParseForm = langParser
    , tbParseRule = parseGentzenFOLJ
    }
