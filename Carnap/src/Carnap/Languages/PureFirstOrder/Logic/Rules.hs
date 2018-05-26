{-#LANGUAGE GADTs, RankNTypes, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Rules where

import Data.List (intercalate)
import Data.Typeable (Typeable)
import Data.Maybe (catMaybes)
import Text.Parsec
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification (applySub,subst)
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Util
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Calculi.NaturalDeduction.Syntax (DeductionLine(..),depth,assertion)

--------------------------------------------------------
--1. FirstOrder Sequent Calculus
--------------------------------------------------------

type FOLSequentCalc = ClassicalSequentOver PureLexiconFOL

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema FOLSequentCalc where 

    appSchema (SeqQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SeqV x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SeqV x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

pattern SeqQuant q        = FX (Lx2 (Lx1 (Lx2 (Bind q))))
pattern SeqSV n           = FX (Lx2 (Lx1 (Lx1 (Lx4 (StaticVar n)))))
pattern SeqVar c a        = FX (Lx2 (Lx1 (Lx4 (Function c a))))
pattern SeqTau c a        = FX (Lx2 (Lx1 (Lx5 (Function c a))))
pattern SeqConst c a      = FX (Lx2 (Lx1 (Lx3 (Function c a))))
pattern SeqV s            = SeqVar (Var s) AZero
pattern SeqT n            = SeqTau (SFunc AZero n) AZero
pattern SeqC n            = SeqConst (Constant n) AZero

instance Eq (FOLSequentCalc a) where
        (==) = (=*)

instance ParsableLex (Form Bool) PureLexiconFOL where
        langParser = folFormulaParser

instance IndexedSchemeConstantLanguage (FOLSequentCalc (Term Int)) where
        taun = SeqT

folSeqParser = seqFormulaParser :: Parsec String u (FOLSequentCalc (Sequent (Form Bool)))

tau :: IndexedSchemeConstantLanguage (FixLang lex (Term Int)) => FixLang lex (Term Int)
tau = taun 1

tau' :: IndexedSchemeConstantLanguage (FixLang lex (Term Int)) => FixLang lex (Term Int)
tau' = taun 2

phi :: (Typeable b, PolyadicSchematicPredicateLanguage (FixLang lex) (Term Int) (Form b))
    => Int -> (FixLang lex) (Term Int) -> (FixLang lex) (Form b)
phi n x = pphin n AOne :!$: x

phi' :: PolyadicSchematicPredicateLanguage (FixLang lex) (Term Int) (Form Bool)
    => Int -> (FixLang lex) (Term Int) -> (FixLang lex) (Form Bool)
phi' n x = pphin n AOne :!$: x

theta :: SchematicPolyadicFunctionLanguage (FixLang lex) (Term Int) (Term Int)
    => (FixLang lex) (Term Int) -> (FixLang lex) (Term Int)
theta x = spfn 1 AOne :!$: x

data DerivedRule = DerivedRule { conclusion :: PureFOLForm, premises :: [PureFOLForm]}
               deriving (Show, Eq)

eigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The constant " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The constant " ++ show c' ++ " appears not to be fresh in the other premise " ++ show suc'
    | otherwise = case c' of 
                          SeqC _ -> Nothing
                          SeqT _ -> Nothing
                          _ -> Just $ "The term " ++ show c' ++ " is not a constant"
    where c'   = applySub sub c
          ant' = applySub sub ant
          suc' = applySub sub suc
          -- XXX : this is not the most efficient way of checking
          -- imaginable.
          occursIn x y = not $ (subst x (static 0) y) =* y

tautologicalConstraint prems conc sub = case prems' of
                 []         | isValid (propForm conc') -> Nothing 
                 (p':ps')   | isValid (propForm $ foldr (./\.) p' ps' .=>. conc') -> Nothing
                 []         | otherwise -> Just $ show conc' ++  " is not truth-functional validity"
                 _          | otherwise -> Just $ show conc' ++  " is not a truth functional consequence of " ++ intercalate ", " (map show prems')
    where prems' = map (applySub sub) prems
          conc'  = applySub sub conc

globalOldConstraint cs (Left ded) lineno sub = 
          if all (\c -> any (\x -> c `occursIn`x) relevantLines) cs'
              then Nothing
              else Just $ "a constant in " ++ show cs' ++ " appears not to be old, but this rule needs old constants"
    where cs' = map (applySub sub) cs

          relevantLines = catMaybes . map (fmap liftLang . assertion) $ 
                            ((oldRelevant [] $ take (lineno - 1) ded) ++ fromsp)

          occursIn x y = not $ (subst x (static 0) y) =* y

          --some extra lines that we need to add if we're putting this
          --constraint on a subproof-closing rule
          fromsp = case ded !! (lineno - 1) of
                       ShowWithLine _ d _ _ -> 
                            case takeWhile (\x -> depth x > d) . drop lineno $ ded of
                               sp@(h:t) -> filter (witnessAt (depth h)) sp
                               [] -> []
                       _ -> []

          oldRelevant accum [] = accum
          oldRelevant [] (d:ded)  = oldRelevant [d] ded 
          oldRelevant (a:accum) (d:ded) = if depth d < depth a 
                                              then let accum' = filter (witnessAt (depth d)) accum in
                                                  oldRelevant (d:accum') ded 
                                              else oldRelevant (d:a:accum) ded 

          witnessAt ldepth (ShowWithLine _ sdepth _ _) = sdepth < ldepth
          witnessAt ldepth l = depth l <= ldepth 

globalNewConstraint cs ded lineno sub = 
        case checkNew of
            Nothing -> Just $ "a constant in " ++ show cs' ++ " appears not to be new, but this rule needs new constants"
            Just s -> Nothing
    where cs' = map (applySub sub) cs
          checkNew = mapM (\c -> globalOldConstraint [c] ded lineno sub) cs

-------------------------
--  1.1. Common Rules  --
-------------------------

type FirstOrderRule lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemeConstantLanguage (ClassicalSequentOver lex (Term Int))
        , QuantLanguage (ClassicalSequentOver lex (Form b)) (ClassicalSequentOver lex (Term Int)) 
        , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        ) => SequentRule lex (Form b)

type FirstOrderEqRule lex b = 
        ( Typeable b
        , EqLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , IndexedSchemeConstantLanguage (ClassicalSequentOver lex (Term Int))
        , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        ) => SequentRule lex (Form b)

eqReflexivity :: FirstOrderEqRule lex b
eqReflexivity = [] ∴ Top :|-: SS (tau `equals` tau)

eqSymmetry :: FirstOrderEqRule lex b
eqSymmetry = [GammaV 1 :|-: SS (tau `equals` tau')] ∴ GammaV 1 :|-: SS (tau `equals` tau')

universalGeneralization :: FirstOrderRule lex b
universalGeneralization = [ GammaV 1 :|-: SS (phi 1 (taun 1))]
                          ∴ GammaV 1 :|-: SS (lall "v" (phi 1))

universalInstantiation :: FirstOrderRule lex b
universalInstantiation = [ GammaV 1 :|-: SS (lall "v" (phi 1))]
                         ∴ GammaV 1 :|-: SS (phi 1 (taun 1))

existentialGeneralization :: FirstOrderRule lex b
existentialGeneralization = [ GammaV 1 :|-: SS (phi 1 (taun 1))]
                            ∴ GammaV 1 :|-: SS (lsome "v" (phi 1))

existentialInstantiation :: FirstOrderRule lex b
existentialInstantiation = [ GammaV 1 :|-: SS (lsome "v" (phi 1))]
                           ∴ GammaV 1 :|-: SS (phi 1 (taun 1))

negatedExistentialInstantiation :: FirstOrderRule lex b
negatedExistentialInstantiation = [ GammaV 1 :|-: SS (lneg $ lsome "v" (phi 1))]
                                  ∴ GammaV 1 :|-: SS (lneg $ phi 1 (taun 1))

negatedUniversalInstantiation :: FirstOrderRule lex b
negatedUniversalInstantiation = [ GammaV 1 :|-: SS (lneg $ lall "v" (phi 1))]
                                ∴ GammaV 1 :|-: SS (lneg $ phi 1 (taun 1))

------------------------------------
--  1.2. Rules with Variations  --
------------------------------------

type FirstOrderEqRuleVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , EqLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , IndexedSchemeConstantLanguage (ClassicalSequentOver lex (Term Int))
        , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , SchematicPolyadicFunctionLanguage (ClassicalSequentOver lex) (Term Int) (Term Int)
        ) => [SequentRule lex (Form b)]
        
type FirstOrderRuleVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemeConstantLanguage (ClassicalSequentOver lex (Term Int))
        , QuantLanguage (ClassicalSequentOver lex (Form b)) (ClassicalSequentOver lex (Term Int)) 
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        ) => [SequentRule lex (Form b)]

leibnizLawVariations :: FirstOrderEqRuleVariants lex b
leibnizLawVariations = [
                           [ GammaV 1 :|-: SS (phi 1 tau)
                           , GammaV 2 :|-: SS (tau `equals` tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phi 1 tau')
                       , 
                           [ GammaV 1 :|-: SS (phi 1 tau')
                           , GammaV 2 :|-: SS (tau `equals` tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phi 1 tau)
                       ]

antiLeibnizLawVariations :: FirstOrderEqRuleVariants lex b
antiLeibnizLawVariations = [
                           [ GammaV 1 :|-: SS (phi 1 tau)
                           , GammaV 2 :|-: SS (lneg $ phi 1 tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ tau `equals` tau') 
                       , 
                           [ GammaV 1 :|-: SS (phi 1 tau)
                           , GammaV 2 :|-: SS (lneg $ phi 1 tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ tau' `equals` tau) 
                       ]

euclidsLawVariations :: FirstOrderEqRuleVariants lex b
euclidsLawVariations = [
                           [ GammaV 2 :|-: SS (tau `equals` tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (theta tau `equals` theta tau')
                       , 
                           [ GammaV 2 :|-: SS (tau `equals` tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (theta tau' `equals` theta tau)
                       ]

existentialDerivation :: FirstOrderRuleVariants lex b
existentialDerivation = [
                            [ GammaV 1 :+:  SA (phi 1 tau) :|-: SS (phin 1) 
                            , GammaV 2 :|-: SS (lsome "v" $ phi 1)   
                            , SA (phi 1 tau) :|-: SS (phi 1 tau)            
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)      
                        ,
                            [ GammaV 1 :|-: SS (phin 1)
                            , SA (phi 1 tau) :|-: SS (phi 1 tau)
                            , GammaV 2 :|-: SS (lsome "v" $ phi 1)
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
                        ]

quantifierNegation :: FirstOrderRuleVariants lex b
quantifierNegation = [  
                        [ GammaV 1 :|-: SS (lneg $ lsome "v" $ phi 1)] 
                        ∴ GammaV 1 :|-: SS (lall "v" $ \x -> lneg $ phi 1 x)
                     ,  [ GammaV 1 :|-: SS (lsome "v" $ \x -> lneg $ phi 1 x)] 
                        ∴ GammaV 1 :|-: SS (lneg $ lall "v"  $ phi 1)
                     ,  [ GammaV 1 :|-: SS (lneg $ lall "v" $ phi 1)] 
                        ∴ GammaV 1 :|-: SS (lsome "v" $ \x -> lneg $ phi 1 x)
                     ,  [ GammaV 1 :|-: SS (lall "v" $ \x -> lneg $ phi 1 x)] 
                        ∴ GammaV 1 :|-: SS (lneg $ lsome "v" $ phi 1)
                     ]
