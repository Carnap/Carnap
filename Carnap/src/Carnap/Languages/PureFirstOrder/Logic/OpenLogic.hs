{-#LANGUAGE ConstraintKinds, StandaloneDeriving, RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.OpenLogic
( parseOpenLogicAxFONK, parseOpenLogicFONK, openLogicFONKCalc, OpenLogicAxFONK(..), OpenLogicFONK(..), olpFOLKCalc, olpFOLJCalc) where

import Text.Parsec
import Data.List
import Data.Char
import Data.Tree
import Data.Map as M (lookup)
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

data OpenLogicFONK lex = PropNK OpenLogicPropNK
                | AllI | AllE
                | ExistsI | ExistsE Int | ExistsEVac
                | EqI     | EqE1 | EqE2
                | ExistsEAnnotated Int (ClassicalSequentOver lex (Term Int))
                | ExistsEAnnotatedVac Int (ClassicalSequentOver lex (Term Int))

deriving instance Eq (ClassicalSequentOver lex (Term Int)) => Eq (OpenLogicFONK lex)

data OpenLogicAxFONK lex = FONK (OpenLogicFONK lex) 
                         | RuntimeAxiom String (ClassicalSequentOver lex (Sequent (Form Bool)))

deriving instance (Eq (ClassicalSequentOver lex (Term Int)), Eq (ClassicalSequentOver lex (Sequent (Form Bool)))) => Eq (OpenLogicAxFONK lex)

data OpenLogicFOLK = LK OpenLogicPropLK 
             | AllL   | AllR
             | ExistL | ExistR

newtype OpenLogicFOLJ = LJ OpenLogicFOLK

instance Show (ClassicalSequentOver lex (Term Int)) => Show (OpenLogicFONK lex) where
    show (PropNK x)                 = show x
    show AllI                       = "∀Intro"
    show AllE                       = "∀Elim"
    show EqI                        = "=Intro"
    show EqE1                       = "=Elim"
    show EqE2                       = "=Elim"
    show ExistsI                    = "∃Intro"
    show (ExistsE n)                = "∃Elim (" ++ show n ++ ")"
    show (ExistsEAnnotated n t)     = "∃Elim " ++ show t ++ " (" ++ show n ++ ")"
    show (ExistsEAnnotatedVac n t)  = "∃Elim " ++ show t ++ " (" ++ show n ++ ")"
    --We need to show the term in order to get the proof hashed correctly when memoizing
    show (ExistsEVac)               = "∃Elim"

instance Show (ClassicalSequentOver lex (Term Int)) => Show (OpenLogicAxFONK lex) where
    show (FONK x)                 = show x
    show (RuntimeAxiom s _)       = "Axiom: " ++ s

instance Show OpenLogicFOLK where 
    show (LK x) = show x
    show AllL   = "∀L"
    show AllR   = "∀R"
    show ExistL = "∃L"
    show ExistR = "∃R"

instance Show OpenLogicFOLJ where
    show (LJ x) = show x
    
parseOpenLogicFOLK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [OpenLogicFOLK]
parseOpenLogicFOLK rtc = try folParse <|> liftProp
        where liftProp = map LK <$> parseOpenLogicPropLK rtc
              folParse = do r <- choice (map (try . string) [ "AL", "@L", "∀L","AR","@R","∀R", "EL","3L", "∃L", "ER", "3R", "∃R" ])
                            return $ (\x -> [x]) $ case r of
                               r | r `elem` ["AL", "@L", "∀L"] -> AllL
                                 | r `elem` ["AR", "@R", "∀R"] -> AllR
                                 | r `elem` ["EL", "3L", "∃L"] -> ExistL
                                 | r `elem` ["ER", "3R", "∃R"] -> ExistR

parseOpenLogicFOLJ :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [OpenLogicFOLJ]
parseOpenLogicFOLJ rtc = map LJ <$> parseOpenLogicFOLK rtc

parseOpenLogicFONK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [OpenLogicFONK lex]
parseOpenLogicFONK rtc = (try folParse <|> liftProp) <* spaces <* eof
        where liftProp = map PropNK <$> parseOpenLogicPropNK rtc
              stringOpts = choice . map (try . string)
              folParse = choice . map try $
                    [ stringOpts ["AIntro", "@Intro", "∀Intro", "AI", "@I", "∀I"] >> return [AllI]
                    , stringOpts ["AElim", "@Elim", "∀Elim", "AE", "@E", "∀E"] >> return [AllE]
                    , stringOpts ["EIntro", "3Intro", "∃Intro", "EI", "3I", "∃I"] >> return [ExistsI]
                    , stringOpts ["=Intro", "=I"] >> return [EqI]
                    , stringOpts ["=Elim", "=E"] >> return [EqE1, EqE2]
                    , (stringOpts ["EElim", "3Elim", "∃Elim", "EE", "3E", "∃E"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [ExistsE val])
                    , stringOpts ["EElim", "3Elim", "∃Elim", "EE", "3E", "∃E"] >> return [ExistsEVac]
                    ]
              getLabel = (char '(' *> many1 digit <* char ')') <|> many1 digit

parseOpenLogicAxFONK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [OpenLogicAxFONK lex]
parseOpenLogicAxFONK rtc = try liftNK <|> parseAxiom
        where liftNK = map FONK <$> parseOpenLogicFONK rtc
              parseAxiom = do string "Ax-"
                              an <- many1 alphaNum
                              case M.lookup (map toLower an) (runtimeAxioms rtc) of
                                  Just rs -> return $ map (\r -> RuntimeAxiom an r) rs
                                  Nothing -> parserFail "Looks like you're citing an axiom that doesn't exist"

type NKAdequate lex = 
         ( BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , QuantLanguage (ClassicalSequentOver lex (Form Bool)) (ClassicalSequentOver lex (Term Int)) 
         , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form Bool)
         , PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) Int Int 
         , PrismIndexedConstant (ClassicalSequentLexOver lex) Int
         , PrismSchematicProp lex Bool
         , PrismBooleanConnLex lex Bool
         , PrismIndexedConstant lex Int
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
         coreRuleOf (ExistsEAnnotated _ t) = parameterExistentialDerivation t
         coreRuleOf (ExistsEAnnotatedVac _ t) = weakExistentialDerivation

         coreRestriction AllI = Just $ eigenConstraint (taun 1) (SS (lall "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction (ExistsEAnnotated _ t) = Just $ eigenConstraint t (SS (lsome "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction (ExistsEAnnotatedVac _ t) = Just $ eigenConstraint t (SS (lsome "v" (phi' 1)) :-: fodelta 1) (fogamma 1)
         coreRestriction _ = Nothing

instance NKAdequate lex => Inference (OpenLogicFONK lex) lex (Form Bool) where
        ruleOf x = coreRuleOf x
        restriction x = coreRestriction x

instance NKAdequate lex => CoreInference (OpenLogicAxFONK lex) lex (Form Bool) where
         coreRuleOf (FONK x) = coreRuleOf x
         coreRuleOf (RuntimeAxiom _ r) = multiCutLeft r ∴ multiCutRight r

         coreRestriction (FONK x) = coreRestriction x
         coreRestriction _ = Nothing

instance NKAdequate lex => Inference (OpenLogicAxFONK lex) lex (Form Bool) where
        ruleOf x = coreRuleOf x
        restriction x = coreRestriction x


instance (Eq r, AssumptionNumbers r, NKAdequate lex) => StructuralInference (OpenLogicFONK lex) lex (ProofTree r lex (Form Bool)) where
    structuralRestriction pt n (PropNK r) = structuralRestriction pt n r
    --ExistsE always throws an error, since we get it only if the
    --structural override fails
    structuralRestriction pt _ (ExistsE n) = Just $ checkAssumptionForm n pt (phi' 1 tau) 
                            `andFurtherRestriction` const (Just "Cannot find any assumption with a term available for this rule")
    structuralRestriction pt _ (ExistsEAnnotated n t) = Just $ checkAssumptionForm n pt (phi' 1 tau)
                            `andFurtherRestriction` exhaustsAssumptions n pt (SS $ phi' 1 t)
    structuralRestriction pt _ (ExistsEAnnotatedVac n t) = Just $ checkAssumptionForm n pt (phi' 1 tau)
                            `andFurtherRestriction` const (Just "Cannot find any assumption with a term available for this rule")
    structuralRestriction pt _ r = Nothing

instance (Eq r, AssumptionNumbers r, NKAdequate lex) => StructuralInference (OpenLogicAxFONK lex) lex (ProofTree r lex (Form Bool)) where
    structuralRestriction pt n (FONK r) = structuralRestriction pt n r
    structuralRestriction pt _ r = Nothing

instance (AssumptionNumbers r, NKAdequate lex) => StructuralOverride (OpenLogicFONK lex) (ProofTree r lex (Form Bool)) where
    structuralOverride pt (ExistsE n) = case freshParametersAt n pt of 
                                            [] -> Nothing
                                            t : _ -> Just [ExistsEAnnotated n t, ExistsEAnnotatedVac n t]
    structuralOverride _ _ = Nothing

instance (AssumptionNumbers r, NKAdequate lex) => StructuralOverride (OpenLogicAxFONK lex) (ProofTree r lex (Form Bool)) where
    structuralOverride pt (FONK r) = map FONK <$> structuralOverride pt r 
    structuralOverride _ _ = Nothing

freshParametersAt n pt@(Node _ [Node p1 _, Node p2 _]) = case leavesLabeled n pt of
        [] -> []
        (Node pl _ : _) -> filter isConst (toListOf termsOf (content pl)) \\ (toListOf termsOf (content p1) ++ toListOf termsOf (content p2)) 
        --we're looking for a constant that's in the assumption but isn't
        --in either premise to the EE inference
    where isConst t = maybe False (const True) (t ^? _constIdx)
freshParametersAt _ _ = []

instance AssumptionNumbers (OpenLogicFONK lex) where
        introducesAssumptions (PropNK r) = introducesAssumptions r
        introducesAssumptions _ = []

        dischargesAssumptions (PropNK r)= dischargesAssumptions r
        dischargesAssumptions (ExistsE n) = [n]
        dischargesAssumptions (ExistsEAnnotated n t) = [n]
        dischargesAssumptions (ExistsEAnnotatedVac n t) = [n]
        dischargesAssumptions _ = []

instance AssumptionNumbers (OpenLogicAxFONK lex) where
        introducesAssumptions (FONK r) = introducesAssumptions r
        introducesAssumptions _ = []

        dischargesAssumptions (FONK r)= dischargesAssumptions r
        dischargesAssumptions _ = []

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
         , PrismSubstitutionalVariable lex
         , ReLex lex
         )

instance LKAdequate lex => CoreInference OpenLogicFOLK lex (Form Bool) where
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

instance SpecifiedUnificationType OpenLogicFOLK

instance LKAdequate lex => CoreInference OpenLogicFOLJ lex (Form Bool) where
         corePremisesOf (LJ x) = corePremisesOf x

         coreConclusionOf (LJ x) = coreConclusionOf x

         coreRestriction (LJ x) = case coreRestriction x of
                                      Nothing -> Just $ \sub -> monoConsequent (applySub sub $ coreConclusionOf x)
                                      Just f -> Just $ \sub -> f sub `mplus` monoConsequent (applySub sub $ coreConclusionOf x)
             where monoConsequent :: forall lex . Eq (ClassicalSequentOver lex (Form Bool)) => ClassicalSequentOver lex (Sequent (Form Bool)) -> Maybe String
                   monoConsequent (_:|-:x)= case nub (toListOf concretes x :: [ClassicalSequentOver lex (Form Bool)]) of
                                              _:_:xs -> Just "LJ requires that the right hand side of each sequent contain at most one formula"
                                              _ -> Nothing

instance SpecifiedUnificationType OpenLogicFOLJ

openLogicFONKCalc :: TableauCalc PureLexiconFOL (Form Bool) (OpenLogicFONK PureLexiconFOL) 
openLogicFONKCalc = mkTBCalc
    { tbParseForm = thomasBolducAndZachFOL2019FormulaParser
    , tbParseRule = parseOpenLogicFONK
    , tbNotation = dropOuterParens
    }

olpFOLKCalc :: TableauCalc PureLexiconFOL (Form Bool) OpenLogicFOLK
olpFOLKCalc = mkTBCalc
    { tbParseForm = thomasBolducAndZachFOL2019FormulaParser 
    , tbParseRule = parseOpenLogicFOLK
    , tbNotation = dropOuterParens
    }

olpFOLJCalc :: TableauCalc PureLexiconFOL (Form Bool) OpenLogicFOLJ
olpFOLJCalc = mkTBCalc
    { tbParseForm = thomasBolducAndZachFOL2019FormulaParser 
    , tbParseRule = parseOpenLogicFOLJ
    , tbNotation = dropOuterParens
    }
