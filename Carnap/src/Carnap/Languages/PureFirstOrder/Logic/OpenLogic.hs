{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.OpenLogic
( parseOpenLogicFONK, openLogicFONKCalc, OpenLogicFONK(..)) where

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
                | ExistsEAnnotated Int (ClassicalSequentOver lex (Term Int))
                | ExistsEAnnotatedVac Int (ClassicalSequentOver lex (Term Int))

instance Show (OpenLogicFONK lex) where
    show (PropNK x)                 = show x
    show AllI                       = "∀Intro"
    show AllE                       = "∀Elim"
    show ExistsI                    = "∃Intro"
    show (ExistsE n)                = "∃Elim (" ++ show n ++ ")"
    show (ExistsEAnnotated n t)     = "∃Elim (" ++ show n ++ ")"
    show (ExistsEAnnotatedVac n t)  = "∃Elim (" ++ show n ++ ")"
    show (ExistsEVac)               = "∃Elim"

parseOpenLogicFONK :: Parsec String u [OpenLogicFONK lex]
parseOpenLogicFONK = try folParse <|> liftProp
        where liftProp = map PropNK <$> parseOLPPropNK
              stringOpts = choice . map (try . string)
              folParse = choice . map try $
                    [ stringOpts ["AIntro", "∀Intro", "AI", "∀I"] >> return [AllI]
                    , stringOpts ["AElim", "∀Elim", "AE", "∀E"] >> return [AllE]
                    , stringOpts ["EIntro", "∃Intro", "EI", "∃I"] >> return [ExistsI]
                    , (stringOpts ["EElim", "∃Elim", "EE", "∃E"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [ExistsE val])
                    , stringOpts ["EElim", "∃Elim", "EE", "∃E"] >> return [ExistsEVac]
                    ]

instance Inference (OpenLogicFONK PureLexiconFOL) PureLexiconFOL (Form Bool) where
        ruleOf x = coreRuleOf x
        restriction x = coreRestriction x

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemeConstantLanguage (ClassicalSequentOver lex (Term Int))
         , QuantLanguage (ClassicalSequentOver lex (Form Bool)) (ClassicalSequentOver lex (Term Int)) 
         , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form Bool)
         , PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) Int Int 
         , PrismIndexedConstant (ClassicalSequentLexOver lex) Int
         , PrismSubstitutionalVariable lex
         , PrismStandardVar (ClassicalSequentLexOver lex) Int
         , CopulaSchema (ClassicalSequentOver lex)
         , Schematizable (lex (ClassicalSequentOver lex))
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , PrismSubstitutionalVariable (ClassicalSequentLexOver lex)
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference (OpenLogicFONK lex) lex (Form Bool) where
         coreRuleOf (PropNK x) = coreRuleOf x
         coreRuleOf AllI = universalGeneralization
         coreRuleOf AllE = universalInstantiation
         coreRuleOf ExistsI = existentialGeneralization
         coreRuleOf (ExistsE _) = weakExistentialDerivation
         coreRuleOf (ExistsEVac) = weakExistentialDerivation
         coreRuleOf (ExistsEAnnotatedVac _ t) = weakExistentialDerivation
         coreRuleOf (ExistsEAnnotated _ t) = parameterExistentialDerivation t

         coreRestriction AllI = Just $ eigenConstraint (taun 1) (SS (lall "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction (ExistsEAnnotated _ t) = Just $ eigenConstraint t (SS (lsome "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction (ExistsEAnnotatedVac _ t) = Just $ eigenConstraint t (SS (lsome "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction _ = Nothing

instance AssumptionNumbers r => StructuralInference (OpenLogicFONK PureLexiconFOL) PureLexiconFOL (ProofTree r PureLexiconFOL (Form Bool)) where
    structuralRestriction pt n (PropNK r) = structuralRestriction pt n r
    --ExistsE always throws an error, since we get it only if the
    --structural override fails
    structuralRestriction pt _ (ExistsE n) = Just $ checkAssumptionForm n pt (phi' 1 tau) 
                            `andFurtherRestriction` const (Just "Cannot find any assumption with a term available for this rule")
    structuralRestriction pt _ (ExistsEAnnotated n t) = Just $ checkAssumptionForm n pt (phi' 1 tau)
                            `andFurtherRestriction` exhaustsAssumptions n pt (SS $ phi' 1 t)
    structuralRestriction pt _ (ExistsEAnnotatedVac n t) = Just $ checkAssumptionForm n pt (phi' 1 tau)
    structuralRestriction pt _ r = Nothing

instance AssumptionNumbers r => StructuralOverride (OpenLogicFONK PureLexiconFOL) (ProofTree r PureLexiconFOL (Form Bool)) where
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
