{-#LANGUAGE RankNTypes, StandaloneDeriving, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses, ConstraintKinds #-}
module Carnap.Languages.PureFirstOrder.Logic.OpenLogic
( parseOpenLogicFONK, openLogicFONKCalc, OpenLogicFONK(..), olpFOLKCalc, olpFOLJCalc) where

import Text.Parsec
import Data.List
import Data.Tree
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
import Carnap.Languages.PureFirstOrder.Logic.Gentzen
import Carnap.Languages.PurePropositional.Logic.OpenLogic
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Languages.Util.GenericConstructors
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.Util
import Carnap.Languages.Util.LanguageClasses

data OpenLogicFONK lex = PropNK OLPPropNK
                | AllI | AllE
                | ExistsI | ExistsE Int | ExistsEVac
                | EqI     | EqE1 | EqE2
                | ExistsEAnnotated Int (ClassicalSequentOver lex (Term Int))
                | ExistsEAnnotatedVac Int (ClassicalSequentOver lex (Term Int))

deriving instance Eq (ClassicalSequentOver lex (Term Int)) => Eq (OpenLogicFONK lex)

instance Show (OpenLogicFONK lex) where
    show (PropNK x)                 = show x
    show AllI                       = "∀Intro"
    show AllE                       = "∀Elim"
    show EqI                        = "=Intro"
    show EqE1                       = "=Elim"
    show EqE2                       = "=Elim"
    show ExistsI                    = "∃Intro"
    show (ExistsE n)                = "∃Elim (" ++ show n ++ ")"
    show (ExistsEAnnotated n t)     = "∃Elim (" ++ show n ++ ")"
    show (ExistsEAnnotatedVac n t)  = "∃Elim (" ++ show n ++ ")"
    show (ExistsEVac)               = "∃Elim"

parseOpenLogicFONK :: Parsec String u [OpenLogicFONK lex]
parseOpenLogicFONK = (try folParse <|> liftProp) <* spaces <* eof
        where liftProp = map PropNK <$> parseOLPPropNK
              stringOpts = choice . map (try . string)
              folParse = choice . map try $
                    [ stringOpts ["AIntro", "∀Intro", "AI", "∀I"] >> return [AllI]
                    , stringOpts ["AElim", "∀Elim", "AE", "∀E"] >> return [AllE]
                    , stringOpts ["EIntro", "∃Intro", "EI", "∃I"] >> return [ExistsI]
                    , stringOpts ["=Intro", "=I"] >> return [EqI]
                    , stringOpts ["=Elim", "=E"] >> return [EqE1, EqE2]
                    , (stringOpts ["EElim", "∃Elim", "EE", "∃E"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [ExistsE val])
                    , stringOpts ["EElim", "∃Elim", "EE", "∃E"] >> return [ExistsEVac]
                    ]
              getLabel = (char '(' *> many1 digit <* char ')') <|> many1 digit

instance NKAdequate lex => Inference (OpenLogicFONK lex) lex (Form Bool) where
        ruleOf x = coreRuleOf x
        restriction x = coreRestriction x

type NKAdequate lex = 
         ( BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , QuantLanguage (ClassicalSequentOver lex (Form Bool)) (ClassicalSequentOver lex (Term Int)) 
         , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form Bool)
         , PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) Int Int 
         , PrismIndexedConstant (ClassicalSequentLexOver lex) Int
         , PrismSchematicProp lex Bool
         , PrismBooleanConnLex lex Bool
         , PrismSubstitutionalVariable lex
         , PrismTermEquality lex Int Bool
         , PrismStandardVar (ClassicalSequentLexOver lex) Int
         , CopulaSchema (ClassicalSequentOver lex)
         , Schematizable (lex (ClassicalSequentOver lex))
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , PrismSubstitutionalVariable (ClassicalSequentLexOver lex)
         , Eq (ClassicalSequentOver lex (Form Bool))
         , Eq (ClassicalSequentOver lex (Succedent (Form Bool)))
         , Eq (ClassicalSequentOver lex (Term Int))
         , BoundVars (ClassicalSequentLexOver lex)
         , ReLex lex
         )

instance NKAdequate lex => CoreInference (OpenLogicFONK lex) lex (Form Bool) where
         coreRuleOf (PropNK x) = coreRuleOf x
         coreRuleOf AllI = universalGeneralization
         coreRuleOf AllE = universalInstantiation
         coreRuleOf EqI  = eqReflexivity
         coreRuleOf EqE1 = leibnizLawVariations !! 0
         coreRuleOf EqE2 = leibnizLawVariations !! 1
         coreRuleOf ExistsI = existentialGeneralization
         coreRuleOf (ExistsE _) = weakExistentialDerivation
         coreRuleOf (ExistsEVac) = weakExistentialDerivation
         coreRuleOf (ExistsEAnnotatedVac _ t) = weakExistentialDerivation
         coreRuleOf (ExistsEAnnotated _ t) = parameterExistentialDerivation t

         coreRestriction AllI = Just $ eigenConstraint (taun 1) (SS (lall "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction (ExistsEAnnotated _ t) = Just $ eigenConstraint t (SS (lsome "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction (ExistsEAnnotatedVac _ t) = Just $ eigenConstraint t (SS (lsome "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction _ = Nothing

instance (Eq r, AssumptionNumbers r, NKAdequate lex) => StructuralInference (OpenLogicFONK lex) lex (ProofTree r lex (Form Bool)) where
    structuralRestriction pt n (PropNK r) = structuralRestriction pt n r
    --ExistsE always throws an error, since we get it only if the
    --structural override fails
    structuralRestriction pt _ (ExistsE n) = Just $ checkAssumptionForm n pt (phi' 1 tau) 
                            `andFurtherRestriction` const (Just "Cannot find any assumption with a term available for this rule")
    structuralRestriction pt _ (ExistsEAnnotated n t) = Just $ checkAssumptionForm n pt (phi' 1 tau)
                            `andFurtherRestriction` exhaustsAssumptions n pt (SS $ phi' 1 t)
    structuralRestriction pt _ (ExistsEAnnotatedVac n t) = Just $ checkAssumptionForm n pt (phi' 1 tau)
    structuralRestriction pt _ r = Nothing

instance (AssumptionNumbers r, NKAdequate lex) => StructuralOverride (OpenLogicFONK lex) (ProofTree r lex (Form Bool)) where
    structuralOverride pt (ExistsE n) = case freshParametersAt n pt of 
                                            [] -> Nothing
                                            t : _ -> Just [ExistsEAnnotated n t, ExistsEAnnotatedVac n t]
    structuralOverride _ _ = Nothing

freshParametersAt n pt@(Node root _) = case leavesLabeled n pt of
        [] -> []
        (Node pl _ : _) -> toListOf termsOf (content pl) \\ toListOf termsOf (content root)

instance AssumptionNumbers (OpenLogicFONK lex) where
        introducesAssumptions (PropNK r) = introducesAssumptions r
        introducesAssumptions _ = []

        dischargesAssumptions (PropNK r)= dischargesAssumptions r
        dischargesAssumptions (ExistsE n) = [n]
        dischargesAssumptions (ExistsEAnnotated n t) = [n]
        dischargesAssumptions (ExistsEAnnotatedVac n t) = [n]
        dischargesAssumptions _ = []

openLogicFONKCalc :: TableauCalc PureLexiconFOL (Form Bool) (OpenLogicFONK PureLexiconFOL) 
openLogicFONKCalc = mkTBCalc
    { tbParseForm = thomasBolducAndZachFOL2019FormulaParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

olpFOLKCalc :: TableauCalc PureLexiconFOL (Form Bool) GentzenFOLK
olpFOLKCalc = gentzenFOLKCalc 
    { tbParseForm = thomasBolducAndZachFOL2019FormulaParser 
    , tbNotation = dropOuterParens
    }

olpFOLJCalc :: TableauCalc PureLexiconFOL (Form Bool) GentzenFOLJ
olpFOLJCalc = gentzenFOLJCalc 
    { tbParseForm = thomasBolducAndZachFOL2019FormulaParser 
    , tbNotation = dropOuterParens
    }
