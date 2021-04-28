{-#LANGUAGE GADTs, UndecidableInstances, ConstraintKinds, RankNTypes, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Rules where

import Data.List (intercalate)
import Data.Typeable (Typeable)
import Data.Maybe (catMaybes)
import Control.Lens (toListOf,preview, Prism')
import Text.Parsec
import Carnap.Core.Data.Util 
import Carnap.Core.Unification.Unification (applySub,occurs,FirstOrder, Equation, pureBNF)
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Languages.PurePropositional.Logic.Rules (exchange, replace)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Util
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Calculi.NaturalDeduction.Syntax (DeductionLine(..),depth,assertion,discharged,justificationOf,inScope, isAssumptionLine)

--------------------------------------------------------
--1. FirstOrder Sequent Calculus
--------------------------------------------------------

type FOLSequentCalc = ClassicalSequentOver PureLexiconFOL

type OpenFOLSequentCalc a = ClassicalSequentOver (PureFirstOrderLexWith a)

--Overlappable since we may want other schemata for sequent languages that contain things like novel quantifiers
instance {-# OVERLAPPABLE #-} 
        ( StaticVar (OpenFOLSequentCalc a)
        , Schematizable (a (OpenFOLSequentCalc a))
        , ReLex a
        ) => CopulaSchema (OpenFOLSequentCalc a) where 

    appSchema q@(Fx _) (LLam f) e = case ( qtype q >>= preview _all >>= \x -> (,) <$> Just x <*> castTo (seqVar x)
                                         , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (seqVar x)
                                         ) of
                                     (Just (x,v), _) -> schematize (All x) (show (f v) : e)
                                     (_, Just (x,v)) -> schematize (Some x) (show (f v) : e)
                                     _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance UniformlyEq (OpenFOLSequentCalc a) => Eq (OpenFOLSequentCalc a b) where
        (==) = (=*)

seqVar :: StandardVarLanguage (FixLang lex (Term Int)) => String -> FixLang lex (Term Int)
seqVar = var

tau :: IndexedSchemeConstantLanguage (FixLang lex (Term Int)) => FixLang lex (Term Int)
tau = taun 1

tau' :: IndexedSchemeConstantLanguage (FixLang lex (Term Int)) => FixLang lex (Term Int)
tau' = taun 2

tau'' :: IndexedSchemeConstantLanguage (FixLang lex (Term Int)) => FixLang lex (Term Int)
tau'' = taun 3

phi :: (Typeable b, PolyadicSchematicPredicateLanguage (FixLang lex) (Term Int) (Form b))
    => Int -> (FixLang lex) (Term Int) -> (FixLang lex) (Form b)
phi n x = pphin n AOne :!$: x

phi3 :: (Typeable b, PolyadicSchematicPredicateLanguage (FixLang lex) (Term Int) (Form b))
    => Int -> (FixLang lex) (Term Int) -> (FixLang lex) (Term Int) -> (FixLang lex) (Term Int) -> (FixLang lex) (Form b)
phi3 n x y z = pphin n AThree :!$: x :!$: y :!$: z

phi4 :: (Typeable b, PolyadicSchematicPredicateLanguage (FixLang lex) (Term Int) (Form b))
    => Int -> (FixLang lex) (Term Int) -> (FixLang lex) (Term Int) -> (FixLang lex) (Term Int) -> (FixLang lex) (Term Int) -> (FixLang lex) (Form b)
phi4 n x y z w = pphin n AFour :!$: x :!$: y :!$: z :!$: w

phi5 :: (Typeable b, PolyadicSchematicPredicateLanguage (FixLang lex) (Term Int) (Form b))
    => Int -> (FixLang lex) (Term Int) -> (FixLang lex) (Term Int) ->(FixLang lex) (Term Int) -> (FixLang lex) (Term Int) -> (FixLang lex) (Term Int) -> (FixLang lex) (Form b)
phi5 n x y z w v = pphin n AFive :!$: x :!$: y :!$: z :!$: w :!$: v

lbind f = LLam $ \x -> LLam $ \y -> LLam $ \z -> f x y z

phi' :: PolyadicSchematicPredicateLanguage (FixLang lex) (Term Int) (Form Bool)
    => Int -> (FixLang lex) (Term Int) -> (FixLang lex) (Form Bool)
phi' n x = pphin n AOne :!$: x

theta :: SchematicPolyadicFunctionLanguage (FixLang lex) (Term Int) (Term Int)
    => (FixLang lex) (Term Int) -> (FixLang lex) (Term Int)
theta x = spfn 1 AOne :!$: x

eigenConstraint :: 
    ( PrismStandardVar (ClassicalSequentLexOver lex) Int
    , PrismIndexedConstant (ClassicalSequentLexOver lex) Int
    , PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) Int Int
    , Schematizable (lex (ClassicalSequentOver lex))
    , FirstOrderLex (lex (ClassicalSequentOver lex))
    , CopulaSchema (ClassicalSequentOver lex)
    , PrismSubstitutionalVariable (ClassicalSequentLexOver lex)
    ) => ClassicalSequentOver lex (Term Int) 
         -> ClassicalSequentOver lex (Succedent (Form Bool)) 
         -> ClassicalSequentOver lex (Antecedent (Form Bool)) 
         -> [Equation (ClassicalSequentOver lex)]
         -> Maybe String
eigenConstraint c suc ant sub
    | (applySub sub c) `occurs` (applySub sub ant) = Just $ "The term " ++ show (applySub sub c) ++ " appears not to be fresh. "
                                                            ++ "Check the dependencies of this inference for occurances of " ++ show (applySub sub c) ++ "."
    | (applySub sub c) `occurs` (applySub sub suc) = Just $ "The term " ++ show (applySub sub c) ++ " appears not to be fresh. "
                                                            ++ "Check the dependencies of this inference for occurances of " ++ show (applySub sub c) ++ "."
    | otherwise = case (applySub sub c) of 
                          _ | not . null $ preview _sfuncIdx' (applySub sub c) -> Nothing
                            | not . null $ preview _constIdx (applySub sub c) -> Nothing
                            | not . null $ preview _varLabel (applySub sub c) -> Nothing
                          _ -> Just $ "The term " ++ show (pureBNF $ applySub sub c) ++ " is not a constant or variable"
    where _sfuncIdx' :: PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) Int Int 
                     => Prism' (ClassicalSequentOver lex (Term Int)) (Int, Arity (Term Int) (Term Int) (Term Int))
          _sfuncIdx' = _sfuncIdx

tautologicalConstraint prems conc sub = case prems' of
                 []         | isValid (propForm conc') -> Nothing 
                 (p':ps')   | isValid (propForm $ foldr (./\.) p' ps' .=>. conc') -> Nothing
                 []         | otherwise -> Just $ show conc' ++  " is not truth-functional validity"
                 _          | otherwise -> Just $ show conc' ++  " is not a truth functional consequence of " ++ intercalate ", " (map show prems')
    where prems' = map (applySub sub) prems
          conc'  = applySub sub conc

totallyFreshConstraint n ded t v sub 
    | any (\x -> v `occurs`x) relevantLines = Just $ show v ++ " appears not to be fresh on line " ++ show n
    | tau' /= (liftToSequent v) = Just "the flagged variable isn't the one used for instantiation."
    | otherwise = Nothing
    where relevantLines = catMaybes . map assertion $ (take (n - 1) ded)
          tau' = applySub sub t

notAssumedConstraint n ded t sub 
    | any (\x -> tau' `occurs` (liftToSequent x)) relevantLines = Just $ show tau' ++ " appears not to be fresh on line " ++ show n
    | otherwise = Nothing
    where relevantLines = catMaybes . map assertion .  filter isAssumptionLine . scopeFilter . take (n - 1) $ ded
          scopeFilter l = map fst . filter (inScope . snd) $ zip l [1 ..]
          inScope m = (>= (depth $ ded !! (m - 1))) . minimum . map depth . drop (m - 1) . take n $ ded
          tau' = applySub sub t

flaggedVariableConstraint n ded suc getFlag sub =
        case targetlinenos of
            [x] | x < min n (length ded) -> checkFlag (ded !! (x - 1))
            _ -> Just "wrong number of lines discharged"

    where targetlinenos = discharged (ded !! (n - 1))
          scope = inScope (ded !! (n - 1))
          forms = catMaybes . map (\n -> liftToSequent <$> assertion (ded !! (n - 1))) $ scope
          suc' = applySub sub suc
          checkFlag x = case justificationOf x of
                            Just rs -> case getFlag (head rs) of
                                Left s -> Just s
                                Right v'| any (\x -> v' `occurs` x) forms -> Just $ "The term " ++ show v' ++ " occurs in one of the dependencies " ++ show forms
                                        | v' `occurs` suc' -> Just $ "The term " ++ show v' ++ " occurs in the conclusion " ++ show suc'
                                        | otherwise -> Nothing
                            _ -> Just "the line cited has no justification"

globalOldConstraint cs (Left ded) lineno sub =
          if all (\c -> any (\x -> c `occurs`x) relevantLines) cs'
              then Nothing
              else Just $ "a constant in " ++ show cs' ++ " appears not to be old, but this rule needs old constants"
    where cs' = map (applySub sub) cs

          relevantLines = catMaybes . map (fmap liftLang . assertion) $
                            ((oldRelevant [] $ take (lineno - 1) ded) ++ fromsp)

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

montagueNewExistentialConstraint cs ded lineno sub = 
        if any (\x -> any (occursIn x) relevantForms) cs' 
            then Just $ "a variable in " ++ show cs' ++ " occurs before this line. This rule requires a variable not occuring (free or bound) on any earlier line"
            else Nothing
    where cs' = map (fromSequent . applySub sub) cs
          relevantLines = take (lineno - 1) ded
          relevantForms = catMaybes $ map assertion relevantLines
          occursIn x y = occurs x y
                         || boundVarOf x y
                         || any (boundVarOf x) (toListOf formsOf y)

montagueNewUniversalConstraint cs ded lineno sub = 
        case relevantForms of
            [] -> Just "No show line found for this rule. But this rule requires a preceeding show line. Remeber to align opening and closing lines of subproofs."
            x:xs | boundVarOf c' x -> if any (occurs c') xs 
                                          then Just $ "The variable " ++ show c' ++ " occurs freely somewhere before the show line of this rule"
                                          else Nothing
            _ -> Just $ "The variable " ++ show c' ++ " is not bound in the show line of this rule."
    where c' = fromSequent $ applySub sub (head cs)
          relevantLines = dropWhile (not . isShow) $ reverse $ take lineno ded 
          --XXX: for now we ignore the complication of making sure these
          --are *available* lines.
          relevantForms = catMaybes $ map assertion relevantLines
          isShow (ShowLine _ d) = d == depth (ded !! (lineno - 1))
          isShow _ = False

-------------------------
--  1.1. Common Rules  --
-------------------------

type FirstOrderConstraints lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemeConstantLanguage (ClassicalSequentOver lex (Term Int))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        , QuantLanguage (ClassicalSequentOver lex (Form b)) (ClassicalSequentOver lex (Term Int)) 
        , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        )

type FirstOrderRule lex b = FirstOrderConstraints lex b => SequentRule lex (Form b)

type FirstOrderEqRule lex b = 
        ( FirstOrderConstraints lex b
        , EqLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        ) => SequentRule lex (Form b)

eqReflexivity :: FirstOrderEqRule lex b
eqReflexivity = [] ∴ Top :|-: SS (tau `equals` tau)

eqSymmetry :: FirstOrderEqRule lex b
eqSymmetry = [GammaV 1 :|-: SS (tau `equals` tau')] ∴ GammaV 1 :|-: SS (tau' `equals` tau)

eqTransitivity :: FirstOrderEqRule lex b
eqTransitivity = [GammaV 1 :|-: SS (tau `equals` tau')
                 , GammaV 1 :|-: SS (tau' `equals` tau'')
                 ] ∴ GammaV 1 :|-: SS (tau `equals` tau'')

eqNegSymmetry :: FirstOrderEqRule lex b
eqNegSymmetry = [GammaV 1 :|-: SS (lneg $ tau `equals` tau')] ∴ GammaV 1 :|-: SS (lneg $ tau' `equals` tau)

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

existentialAssumption :: FirstOrderRule lex b
existentialAssumption = [ GammaV 1 :|-: SS (lsome "v" (phi 1))]
                        ∴ GammaV 1 :+: SA (phi 1 (taun 1)) :|-: SS (phi 1 (taun 1))

existentialAssumptionDischarge :: FirstOrderRule lex b
existentialAssumptionDischarge = [ GammaV 1 :+: SA (phi 1 (taun 1)) :|-: SS (phi 1 (taun 1))
                                 , GammaV 2 :+: SA (phi 1 (taun 1)) :|-: SS (phin 1) ]
                                 ∴ GammaV 2 :|-: SS (phin 1)

weakExistentialDerivation :: FirstOrderRule lex b
weakExistentialDerivation = [ GammaV 1 :|-: SS (phin 1)
                            , GammaV 2 :|-: SS (lsome "v" $ phi 1)
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)

parameterExistentialDerivation :: FixLang (ClassicalSequentLexOver lex) (Term Int) -> FirstOrderRule lex b
parameterExistentialDerivation t = [ GammaV 1 :+:  SA (phi 1 t) :|-: SS (phin 1) 
                                   , GammaV 2 :|-: SS (lsome "v" $ phi 1)   
                                   ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)      

negatedExistentialInstantiation :: FirstOrderRule lex b
negatedExistentialInstantiation = [ GammaV 1 :|-: SS (lneg $ lsome "v" (phi 1))]
                                  ∴ GammaV 1 :|-: SS (lneg $ phi 1 (taun 1))

negatedUniversalInstantiation :: FirstOrderRule lex b
negatedUniversalInstantiation = [ GammaV 1 :|-: SS (lneg $ lall "v" (phi 1))]
                                ∴ GammaV 1 :|-: SS (lneg $ phi 1 (taun 1))

conditionalExistentialDerivation :: FirstOrderRule lex b
conditionalExistentialDerivation = [ GammaV 1 :|-: SS (lsome "v" (phi 1))
                                   , GammaV 2 :|-: SS (phi 1 (taun 1) .→. phin 1)
                                   ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)

------------------------------------
--  1.2. Rules with Variations  --
------------------------------------

type FirstOrderRuleVariants lex b = FirstOrderConstraints lex b => [SequentRule lex (Form b)]

type FirstOrderEqRuleVariants lex b = 
        ( FirstOrderConstraints lex b 
        , EqLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , SchematicPolyadicFunctionLanguage (ClassicalSequentOver lex) (Term Int) (Term Int)
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
        
        
quantifierNegation ::  FirstOrderRuleVariants lex b
quantifierNegation = exchange (lneg $ lsome "v" $ phi 1) (lall "v" $ lneg . phi 1) 
                     ++ exchange (lsome "v" $ lneg . phi 1) (lneg $ lall "v" $ phi 1)
                     ++ exchange (lneg $ lsome "v" $ lneg . phi 1) (lall "v" $ phi 1)
                     ++ exchange (lsome "v" $ phi 1) (lneg $ lall "v" $ lneg . phi 1)

-------------------------------
--  1.2.2 Replacement Rules  --
-------------------------------

firstOrderReplace :: QuantContextLang (ClassicalSequentOver lex) b Int => 
        ClassicalSequentOver lex (Term Int -> Term Int -> Term Int -> Form b) -> 
        ClassicalSequentOver lex (Term Int -> Term Int -> Term Int -> Form b) -> FirstOrderRuleVariants lex b
firstOrderReplace x y = [ [GammaV 1  :|-: SS (quantCtx 1 AThree x)] ∴ GammaV 1  :|-: SS (quantCtx 1 AThree y)
                        , [GammaV 1  :|-: SS (quantCtx 1 AThree y)] ∴ GammaV 1  :|-: SS (quantCtx 1 AThree x)]

quantifierNegationReplace :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
quantifierNegationReplace = firstOrderReplace (lbind $ \x y z -> lneg $ lsome "v" $ phi4 1 x y z ) (lbind $ \x y z -> lall "v" $ lneg . phi4 1 x y z) 
                         ++ firstOrderReplace (lbind $ \x y z -> lsome "v" $ lneg . phi4 1 x y z) (lbind $ \x y z -> lneg $ lall "v" $ phi4 1 x y z)

quantifierDoubleNegationReplace :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
quantifierDoubleNegationReplace = firstOrderReplace (lbind $ \x y z -> lneg $ lsome "v" $ lneg . phi4 1 x y z ) (lbind $ \x y z -> lall "v" $ phi4 1 x y z) 
                               ++ firstOrderReplace (lbind $ \x y z -> lneg $ lall "v" $ lneg . phi4 1 x y z) (lbind $ \x y z -> lsome "v" $ phi4 1 x y z)

andCommutativity :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
andCommutativity = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. phi3 2 x y z) 
                                     (lbind $ \x y z -> phi3 2 x y z ./\. phi3 1 x y z)

andAssociativity :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
andAssociativity = firstOrderReplace (lbind $ \x y z -> (phi3 1 x y z ./\. phi3 2 x y z) ./\. phi3 3 x y z) 
                                     (lbind $ \x y z -> phi3 1 x y z ./\. (phi3 2 x y z ./\. phi3 3 x y z))

andIdempotence :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
andIdempotence = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. phi3 1 x y z) 
                                   (lbind $ \x y z -> phi3 1 x y z)

andDistributivity :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
andDistributivity = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (phi3 2 x y z .\/. phi3 3 x y z)) 
                                      (lbind $ \x y z -> (phi3 1 x y z ./\. phi3 2 x y z) .\/. (phi3 1 x y z ./\. phi3 3 x y z))
                    ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z .\/. phi3 3 x y z) ./\. phi3 1 x y z) 
                                      (lbind $ \x y z -> (phi3 2 x y z ./\. phi3 1 x y z ) .\/. (phi3 3 x y z ./\. phi3 1 x y z ))
orCommutativity :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
orCommutativity = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. phi3 2 x y z) 
                                    (lbind $ \x y z -> phi3 2 x y z .\/. phi3 1 x y z)

orAssociativity :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
orAssociativity = firstOrderReplace (lbind $ \x y z -> (phi3 1 x y z .\/. phi3 2 x y z) .\/. phi3 3 x y z) 
                                    (lbind $ \x y z -> phi3 1 x y z .\/. (phi3 2 x y z .\/. phi3 3 x y z))

orIdempotence :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
orIdempotence = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. phi3 1 x y z) 
                                  (lbind $ \x y z -> phi3 1 x y z)

orDistributivity :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
orDistributivity = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (phi3 2 x y z ./\. phi3 3 x y z)) 
                                     (lbind $ \x y z -> (phi3 1 x y z .\/. phi3 2 x y z) ./\. (phi3 1 x y z .\/. phi3 3 x y z))
                   ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z ./\. phi3 3 x y z) .\/. phi3 1 x y z  ) 
                                     (lbind $ \x y z -> (phi3 2 x y z .\/. phi3 1 x y z ) ./\. (phi3 3 x y z .\/. phi3 1 x y z ))
iffCommutativity :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
iffCommutativity = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .<=>. phi3 2 x y z) 
                                     (lbind $ \x y z -> phi3 2 x y z .<=>. phi3 1 x y z)

deMorgansLaws :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
deMorgansLaws = firstOrderReplace (lbind $ \x y z -> lneg $ phi3 1 x y z ./\. phi3 2 x y z) 
                                  (lbind $ \x y z -> lneg (phi3 1 x y z) .\/. lneg (phi3 2 x y z))
             ++ firstOrderReplace (lbind $ \x y z -> lneg $ phi3 1 x y z .\/. phi3 2 x y z) 
                                  (lbind $ \x y z -> lneg (phi3 1 x y z) ./\. lneg (phi3 2 x y z))

doubleNegatingDeMorgansLaws :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
doubleNegatingDeMorgansLaws = firstOrderReplace (lbind $ \x y z -> lneg ((lneg $ phi3 1 x y z) ./\. phi3 2 x y z)) 
                                                (lbind $ \x y z -> phi3 1 x y z .\/. lneg (phi3 2 x y z))
                           ++ firstOrderReplace (lbind $ \x y z -> lneg ((lneg $ phi3 1 x y z) .\/. phi3 2 x y z)) 
                                                (lbind $ \x y z -> phi3 1 x y z ./\. lneg (phi3 2 x y z))
                           ++ firstOrderReplace (lbind $ \x y z -> lneg (phi3 1 x y z ./\. (lneg $ phi3 2 x y z))) 
                                                (lbind $ \x y z -> lneg (phi3 1 x y z) .\/. phi3 2 x y z)
                           ++ firstOrderReplace (lbind $ \x y z -> lneg (phi3 1 x y z .\/. (lneg $ phi3 2 x y z))) 
                                                (lbind $ \x y z -> lneg (phi3 1 x y z) ./\. phi3 2 x y z)
                           ++ firstOrderReplace (lbind $ \x y z -> lneg ((lneg $ phi3 1 x y z) ./\. (lneg $ phi3 2 x y z))) 
                                                (lbind $ \x y z -> phi3 1 x y z .\/. phi3 2 x y z)
                           ++ firstOrderReplace (lbind $ \x y z -> lneg ((lneg $ phi3 1 x y z) .\/. (lneg $ phi3 2 x y z))) 
                                                (lbind $ \x y z -> phi3 1 x y z ./\. phi3 2 x y z)


doubleNegation :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
doubleNegation = firstOrderReplace (lbind $ \x y z -> lneg $ lneg $ phi3 1 x y z) 
                                   (lbind $ \x y z -> phi3 1 x y z)

materialConditional :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
materialConditional = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .=>. phi3 2 x y z) 
                                        (lbind $ \x y z -> lneg (phi3 1 x y z) .\/. phi3 2 x y z)
                   ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. phi3 2 x y z) 
                                        (lbind $ \x y z -> lneg (phi3 1 x y z) .=>. phi3 2 x y z)

negatedConditional :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
negatedConditional = firstOrderReplace (lbind $ \x y z -> lneg $ phi3 1 x y z .=>. phi3 2 x y z) 
                                       (lbind $ \x y z -> phi3 1 x y z ./\. (lneg $ phi3 2 x y z))

contraposition :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
contraposition = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .=>. phi3 2 x y z) 
                                   (lbind $ \x y z -> lneg (phi3 2 x y z) .=>. lneg (phi3 1 x y z))

doubleNegatingContraposition :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
doubleNegatingContraposition = firstOrderReplace (lbind $ \x y z -> lneg (phi3 1 x y z) .=>. phi3 2 x y z) 
                                                 (lbind $ \x y z -> lneg (phi3 2 x y z) .=>. phi3 1 x y z)
                            ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .=>. lneg (phi3 2 x y z))
                                                 (lbind $ \x y z -> phi3 2 x y z .=>. lneg (phi3 1 x y z))

exportation :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
exportation = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .=>. (phi3 2 x y z .=>. phi3 3 x y z)) 
                                (lbind $ \x y z -> (phi3 1 x y z ./\. phi3 2 x y z) .=>. phi3 3 x y z)

distribution :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
distribution = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (phi3 2 x y z .\/. phi3 3 x y z)) 
                                 (lbind $ \x y z -> (phi3 1 x y z ./\. phi3 2 x y z) .\/. (phi3 1 x y z ./\. phi3 3 x y z)) 
            ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (phi3 2 x y z ./\. phi3 3 x y z)) 
                                 (lbind $ \x y z -> (phi3 1 x y z .\/. phi3 2 x y z) ./\. (phi3 1 x y z .\/. phi3 3 x y z))

biconditionalExchange :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
biconditionalExchange = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .<=>. phi3 2 x y z) 
                                          (lbind $ \x y z -> (phi3 1 x y z .=>. phi3 2 x y z) ./\. (phi3 2 x y z .=>. phi3 1 x y z))

biconditionalCases :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
biconditionalCases = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .<=>. phi3 2 x y z) 
                                       (lbind $ \x y z -> (phi3 1 x y z ./\. phi3 2 x y z) .\/. (lneg (phi3 1 x y z) ./\. lneg (phi3 2 x y z)))

andTautCancellation :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
andTautCancellation = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (phi3 2 x y z .\/. lneg (phi3 2 x y z))) (lbind $ \x y z -> phi3 1 x y z)
                   ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z .\/. lneg (phi3 2 x y z)) ./\. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)
                   ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (lneg (phi3 2 x y z) .\/. phi3 2 x y z)) (lbind $ \x y z -> phi3 1 x y z)
                   ++ firstOrderReplace (lbind $ \x y z -> (lneg (phi3 2 x y z) .\/. phi3 2 x y z) ./\. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)

andContCancellation :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
andContCancellation = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (phi3 2 x y z ./\. lneg (phi3 2 x y z))) (lbind $ \x y z -> phi3 2 x y z ./\. lneg (phi3 2 x y z))
                   ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z ./\. lneg (phi3 2 x y z)) ./\. phi3 1 x y z) (lbind $ \x y z -> phi3 2 x y z ./\. lneg (phi3 2 x y z))
                   ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (lneg (phi3 2 x y z) ./\. phi3 2 x y z)) (lbind $ \x y z -> lneg (phi3 2 x y z) ./\. phi3 2 x y z)
                   ++ firstOrderReplace (lbind $ \x y z -> (lneg (phi3 2 x y z) ./\. phi3 2 x y z) ./\. phi3 1 x y z) (lbind $ \x y z -> lneg (phi3 2 x y z) ./\. phi3 2 x y z)

orContCancellation :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
orContCancellation = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (phi3 2 x y z ./\. lneg (phi3 2 x y z))) (lbind $ \x y z -> phi3 1 x y z)
                  ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z ./\. lneg (phi3 2 x y z)) .\/. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)
                  ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (lneg (phi3 2 x y z) ./\. phi3 2 x y z)) (lbind $ \x y z -> phi3 1 x y z)
                  ++ firstOrderReplace (lbind $ \x y z -> (lneg (phi3 2 x y z) ./\. phi3 2 x y z) .\/. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)

orTautCancellation :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
orTautCancellation = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (phi3 2 x y z .\/. lneg (phi3 2 x y z))) (lbind $ \x y z -> phi3 2 x y z .\/. lneg (phi3 2 x y z))
                  ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z .\/. lneg (phi3 2 x y z)) .\/. phi3 1 x y z) (lbind $ \x y z -> phi3 2 x y z .\/. lneg (phi3 2 x y z))
                  ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (lneg (phi3 2 x y z) .\/. phi3 2 x y z)) (lbind $ \x y z -> lneg (phi3 2 x y z) .\/. phi3 2 x y z)
                  ++ firstOrderReplace (lbind $ \x y z -> (lneg (phi3 2 x y z) .\/. phi3 2 x y z) .\/. phi3 1 x y z) (lbind $ \x y z -> lneg (phi3 2 x y z) .\/. phi3 2 x y z)

andAbsorption :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
andAbsorption = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (phi3 1 x y z .\/. phi3 2 x y z)) (lbind $ \x y z -> phi3 1 x y z)
             ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z ./\. (phi3 2 x y z .\/. phi3 1 x y z)) (lbind $ \x y z -> phi3 1 x y z)
             ++ firstOrderReplace (lbind $ \x y z -> (phi3 1 x y z .\/. phi3 2 x y z) ./\. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)
             ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z .\/. phi3 1 x y z) ./\. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)

orAbsorption :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
orAbsorption = firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (phi3 1 x y z ./\. phi3 2 x y z)) (lbind $ \x y z -> phi3 1 x y z) 
            ++ firstOrderReplace (lbind $ \x y z -> phi3 1 x y z .\/. (phi3 2 x y z ./\. phi3 1 x y z)) (lbind $ \x y z -> phi3 1 x y z)
            ++ firstOrderReplace (lbind $ \x y z -> (phi3 1 x y z ./\. phi3 2 x y z) .\/. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)
            ++ firstOrderReplace (lbind $ \x y z -> (phi3 2 x y z ./\. phi3 1 x y z) .\/. phi3 1 x y z) (lbind $ \x y z -> phi3 1 x y z)

rulesOfPassage :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
rulesOfPassage = firstOrderReplace (lbind $ \x y z -> lsome "v" $ \w -> phi4 1 x y z w .\/. phi3 2 x y z) 
                                   (lbind $ \x y z -> lsome "v" (\w -> phi4 1 x y z w) .\/. phi3 2 x y z)
                 ++ firstOrderReplace (lbind $ \x y z -> lall "v" $ \w -> phi4 1 x y z w .\/. phi3 2 x y z) 
                                   (lbind $ \x y z -> lall "v" (\w -> phi4 1 x y z w) .\/. phi3 2 x y z)
                 ++ firstOrderReplace (lbind $ \x y z -> lsome "v" $ \w -> phi4 1 x y z w ./\. phi3 2 x y z) 
                                   (lbind $ \x y z -> lsome "v" (\w -> phi4 1 x y z w) ./\. phi3 2 x y z)
                 ++ firstOrderReplace (lbind $ \x y z -> lall "v" $ \w -> phi4 1 x y z w ./\. phi3 2 x y z) 
                                   (lbind $ \x y z -> lall "v" (\w -> phi4 1 x y z w) ./\. phi3 2 x y z)
                 ++ firstOrderReplace (lbind $ \x y z -> lsome "v" $ \w -> phi3 1 x y z .\/. phi4 2 x y z w) 
                                   (lbind $ \x y z ->  phi3 1 x y z .\/. lsome "v" (\w -> phi4 2 x y z w))
                 ++ firstOrderReplace (lbind $ \x y z -> lall "v" $ \w -> phi3 1 x y z .\/. phi4 2 x y z w) 
                                   (lbind $ \x y z ->  phi3 1 x y z .\/. lall "v" (\w -> phi4 2 x y z w))
                 ++ firstOrderReplace (lbind $ \x y z -> lsome "v" $ \w -> phi3 1 x y z ./\. phi4 2 x y z w) 
                                   (lbind $ \x y z ->  phi3 1 x y z ./\. lsome "v" (\w -> phi4 2 x y z w))
                 ++ firstOrderReplace (lbind $ \x y z -> lall "v" $ \w -> phi3 1 x y z ./\. phi4 2 x y z w) 
                                   (lbind $ \x y z -> phi3 1 x y z ./\. lall "v" (\w -> phi4 2 x y z w))

conditionalRulesOfPassage :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
conditionalRulesOfPassage = firstOrderReplace (lbind $ \x y z -> lall "v" $ \w -> phi3 1 x y z .=>. phi4 2 x y z w) 
                                   (lbind $ \x y z -> phi3 1 x y z .=>. lall "v" (\w -> phi4 2 x y z w))
                         ++ firstOrderReplace (lbind $ \x y z -> lsome "v" $ \w -> phi3 1 x y z .=>. phi4 2 x y z w) 
                                   (lbind $ \x y z -> phi3 1 x y z .=>. lsome "v" (\w -> phi4 2 x y z w))
                         ++ firstOrderReplace (lbind $ \x y z -> lall "v" $ \w -> phi4 1 x y z w .=>. phi3 2 x y z) 
                                   (lbind $ \x y z -> lsome "v" (\w -> phi4 1 x y z w) .=>. phi3 2 x y z)
                         ++ firstOrderReplace (lbind $ \x y z -> lsome "v" $ \w -> phi4 1 x y z w .=>. phi3 2 x y z) 
                                   (lbind $ \x y z -> lall "v" (\w -> phi4 1 x y z w) .=>. phi3 2 x y z)

quantifierExchange :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
quantifierExchange = firstOrderReplace (lbind $ \x y z -> lsome "v" $ \v -> lsome "w" $ \w -> phi5 1 x y z w v) 
                                      (lbind $ \x y z -> lsome "w" $ \w -> lsome "v" $ \v -> phi5 1 x y z w v) 
                    ++ firstOrderReplace (lbind $ \x y z -> lall "v" $ \v -> lall "w" $ \w -> phi5 1 x y z w v) 
                                      (lbind $ \x y z -> lall "w" $ \w -> lall "v" $ \v -> phi5 1 x y z w v)

quantifierDistribution :: QuantContextLang (ClassicalSequentOver lex) b Int => FirstOrderRuleVariants lex b
quantifierDistribution = firstOrderReplace (lbind $ \x y z -> lsome "v" $ \w -> phi4 1 x y z w .\/. phi4 2 x y z w)
                                   (lbind $ \x y z -> lsome "v" (\w -> phi4 1 x y z w) .\/. lsome "v" (\w -> phi4 2 x y z w))
                      ++ firstOrderReplace (lbind $ \x y z -> lall "v" $ \w -> phi4 1 x y z w ./\. phi4 2 x y z w) 
                                   (lbind $ \x y z -> lall "v" (\w -> phi4 1 x y z w) ./\. lall "v" (\w -> phi4 2 x y z w))

eqSymmetryReplacement :: (QuantContextLang (ClassicalSequentOver lex) b Int , EqLanguage (ClassicalSequentOver lex) (Term Int) (Form b)) => FirstOrderRuleVariants lex b 
eqSymmetryReplacement = firstOrderReplace (lbind $ \x y z -> x `equals` y) (lbind $ \x y z -> y `equals` x)
