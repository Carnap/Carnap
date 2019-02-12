{-#LANGUAGE GADTs, PatternSynonyms, FlexibleContexts, RankNTypes, FlexibleInstances, MultiParamTypeClasses, TypeOperators #-}
module Carnap.Languages.ModalPropositional.Logic.Rules (
    module Carnap.Languages.ModalPropositional.Logic.Rules,
    module Carnap.Languages.PurePropositional.Logic.Rules
    )

where

import Text.Parsec
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Types
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.ModalPropositional.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Calculi.NaturalDeduction.Syntax (DeductionLine(..),depth,assertion)
import Data.Typeable
import Data.List (intercalate)
import Data.Maybe (catMaybes)

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type WorldTheorySequentCalc = ClassicalSequentOver WorldTheoryPropLexicon

type WorldTheorySequentCalcLex = ClassicalSequentLexOver WorldTheoryPropLexicon

type CoreCalcLex = ClassicalSequentLexOver CoreLexicon

type CoreCalcSeq = ClassicalSequentOver CoreLexicon

type AbsoluteModalPropSequentCalc = ClassicalSequentOver AbsoluteModalPropLexicon

type AbsoluteModalPropSequentCalcLex = ClassicalSequentLexOver AbsoluteModalPropLexicon

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema WorldTheorySequentCalc where
    appSchema (SeqQuant (All x)) (LLam f) e = schematize (All x) (show (f $ liftToSequent $ worldVar x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ liftToSequent $ worldVar x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance CopulaSchema AbsoluteModalPropSequentCalc

pattern SeqP x arity      = FX (Lx2 (Lx1 (Lx1 (Predicate x arity))))
pattern SeqSP x arity     = FX (Lx2 (Lx1 (Lx2 (Predicate x arity))))
pattern SeqCon x arity    = FX (Lx2 (Lx1 (Lx3 (Connective x arity))))
pattern SeqBox            = FX (Lx2 (Lx1 (Lx4 (Connective Box AOne))))
pattern SeqDia            = FX (Lx2 (Lx1 (Lx4 (Connective Diamond AOne))))
pattern SeqIndexer        = FX (Lx2 (Lx2 (Lx1 AtIndex)))
pattern SeqIndicies c a   = FX (Lx2 (Lx2 (Lx2 (Function c a))))
pattern SeqIdxCons c a    = FX (Lx2 (Lx2 (Lx3 (Function c a))))
pattern SeqSchemIdx c a   = FX (Lx2 (Lx2 (Lx4 (Function c a))))
pattern SeqQuant q        = FX (Lx2 (Lx2 (Lx5 (Bind q))))
pattern SeqSchemPred c a  = FX (Lx2 (Lx2 (Lx6 (Predicate c a))))
pattern LFalsum           = FX (Lx2 (Lx1 (Lx5 (Connective Falsum AZero))))
pattern LVerum            = FX (Lx2 (Lx1 (Lx5 (Connective Verum AZero))))
pattern SeqSV n           = FX (Lx2 (Lx1 (Lx6 (StaticVar n))))
pattern SeqProp n         = SeqP (Prop n) AZero
pattern SeqPhi :: Int -> WorldTheorySequentCalc (Form (World -> Bool))
pattern SeqPhi n          = SeqSP (SProp n) AZero
pattern SeqPhiA :: Int -> AbsoluteModalPropSequentCalc (Form (World -> Bool))
pattern SeqPhiA n         = SeqSP (SProp n) AZero
pattern SeqPPhi n         = SeqSchemPred (SPred AOne n) AOne
pattern SeqAnd            = SeqCon And ATwo
pattern SeqOr             = SeqCon Or ATwo
pattern SeqIf             = SeqCon If ATwo
pattern SeqIff            = SeqCon Iff ATwo
pattern SeqNot            = SeqCon Not AOne
pattern SeqNec x          = SeqBox :!$: x
pattern SeqPos x          = SeqDia :!$: x
pattern (:&-:) x y        = SeqAnd :!$: x :!$: y
pattern (:||-:) x y       = SeqOr  :!$: x :!$: y
pattern (:->-:) x y       = SeqIf  :!$: x :!$: y
pattern (:<->-:) x y      = SeqIff :!$: x :!$: y
pattern (:/:) x y         = SeqIndexer :!$: x :!$: y
pattern SeqNeg x          = SeqNot :!$: x
pattern SeqBind q f       = SeqQuant q :!$: LLam f
pattern SeqIndex n        = SeqIndicies (Index n) AZero
pattern SeqSchmIdx n      = SeqSchemIdx (SFunc AZero n) AZero
pattern TheWorld          = SeqIndex 0
pattern SomeWorld         = SeqSchmIdx 0
pattern SomeOtherWorld    = SeqSchmIdx 1
pattern SomeThirdWorld    = SeqSchmIdx 2
pattern SeqCons x y       = SeqIdxCons Cons ATwo :!$: x :!$: y

eigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The index " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The index " ++ show c' ++ " appears not to be fresh, because it occurs in " ++ show suc'
    | otherwise = case c' of 
                          TheWorld -> Just "the index '0' is never counts as fresh, since it has a special meaning"
                          _ -> Nothing
    where c'   = applySub sub c
          ant' = applySub sub ant
          suc' = applySub sub suc
          -- XXX : this is not the most efficient way of checking
          -- imaginable.
          occursIn x y = not $ (subst x (static 0) y) =* y

globalEigenConstraint c (Left ded) lineno sub =
        case foundIn ded 1 of
            Just (f,n) -> Just $ "the index " ++ show c' ++ " appears not to be fresh - it occurs in " ++ show f ++ " on line " ++ show n
            Nothing -> case c' of
                          TheWorld -> Just "the index '0' is never counts as fresh, since it has a special meaning"
                          _ -> Nothing
    where c' = applySub sub c
          foundIn [] n = Nothing
          foundIn (d:ded') n = case assertion d of
                                   Just f | n >= lineno -> Nothing
                                          | c' `occursIn` (liftLang f) -> Just (f, n)
                                          | otherwise -> foundIn ded' (n + 1)
                                   Nothing -> foundIn ded' (n + 1)
          occursIn x y = not $ (subst x (static 0) y) =* y

globalOldConstraint idxes (Left ded) lineno sub = 
          if all (\idx -> idx =* TheWorld || any (\x -> idx `occursIn`x) relevantLines) idxes'
              then Nothing
              else Just $ "an index in " ++ show idxes' ++ " appears not to be old, but this rule needs old indexes"
    where idxes' = map (applySub sub) idxes

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

globalNewConstraint idxes ded lineno sub = 
        case globalOldConstraint idxes ded lineno sub of
            Nothing -> Just $ "an index in " ++ show idxes' ++ " appears not to be new, but this rule needs new indexes"
            Just s -> Nothing
    where idxes' = map (applySub sub) idxes

instance Eq (WorldTheorySequentCalc a) where
        (==) = (=*)


phi :: PolyadicSchematicPredicateLanguage (FixLang lex) (Term World) (Form (World -> Bool)) => Int -> (FixLang lex) (Term World) -> (FixLang lex) (Form (World -> Bool))
phi n x = pphin n AOne :!$: x

wtlgamma :: Int -> WorldTheorySequentCalc (Antecedent (Form (World -> Bool)))
wtlgamma = GammaV

absgamma :: Int -> AbsoluteModalPropSequentCalc (Antecedent (Form Bool))
absgamma = GammaV

someWorld :: IndexingLang lex (Term World) (Form c) (Form (World -> Bool)) => FixLang lex (Term World)
someWorld = worldScheme 0 

someOtherWorld :: IndexingLang lex (Term World) (Form c) (Form (World -> Bool)) => FixLang lex (Term World)
someOtherWorld = worldScheme 1 

someThirdWorld :: IndexingLang lex (Term World) (Form c) (Form (World -> Bool)) => FixLang lex (Term World)
someThirdWorld = worldScheme 2

worldTheorySeqParser = seqFormulaParser :: Parsec String u (WorldTheorySequentCalc (Sequent (Form (World -> Bool))))

absoluteModalPropSeqParser = liftAbsSeq TheWorld <$> (seqFormulaParser :: Parsec String u (AbsoluteModalPropSequentCalc (Sequent (Form (World -> Bool)))))

liftAbsRule (SequentRule p c) = map (liftAbsSeq SomeWorld) p ∴ liftAbsSeq SomeWorld c

liftAbsSeq :: AbsoluteModalPropSequentCalc (Term World) -> AbsoluteModalPropSequentCalc (Sequent (Form (World -> Bool))) -> AbsoluteModalPropSequentCalc (Sequent (Form Bool))
liftAbsSeq w (a :|-: s) = atSomeAnt a :|-: atSomeSuc s
    where 
          atSomeAnt :: AbsoluteModalPropSequentCalc (Antecedent (Form (World -> Bool))) -> AbsoluteModalPropSequentCalc (Antecedent (Form Bool))
          atSomeAnt (x :+: y) = atSomeAnt x :+: atSomeAnt y
          atSomeAnt (SA x) = SA (x :/: w) 
          atSomeAnt (GammaV n) = GammaV n
          atSomeAnt Top = Top

          atSomeSuc :: AbsoluteModalPropSequentCalc (Succedent (Form (World -> Bool))) -> AbsoluteModalPropSequentCalc (Succedent (Form Bool))
          atSomeSuc (x :-: y) = atSomeSuc x :-: atSomeSuc y
          atSomeSuc (SS x) = SS (x :/: w) 
          atSomeSuc Bot = Bot

-------------------------
--  1.1 Standard Rules  --
-------------------------
--Rules found in many systems of propositional logic

type ModalRule lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , PrismCons (ClassicalSequentLexOver lex) World
        , ModalLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexingLang (ClassicalSequentLexOver lex) (Term World) (Form b) (Form (World -> Bool))
        ) => SequentRule lex (Form b)

type QuantModalRule lex b = 
        ( Typeable b
        , QuantLanguage (ClassicalSequentOver lex (Form(World->Bool))) (ClassicalSequentOver lex (Term (World))) 
        , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term World) (Form (World -> Bool))
        , BooleanLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , PrismCons (ClassicalSequentLexOver lex) World
        , ModalLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexingLang (ClassicalSequentLexOver lex) (Term World) (Form b) (Form (World -> Bool))
        ) => SequentRule lex (Form b)

worldlyFalsumElimination :: ModalRule lex b
worldlyFalsumElimination = [ GammaV 1 :|-: SS (lfalsum ./. someWorld)
                           ] ∴ GammaV 1 :|-: SS (phin 1 ./. someOtherWorld)

worldlyFalsumIntroduction :: ModalRule lex b
worldlyFalsumIntroduction = [ GammaV 1 :|-: SS ((lneg $ phin 1) ./. someWorld)
                            , GammaV 2 :|-: SS (phin 1 ./. someWorld)
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lfalsum ./. someOtherWorld)

worldTheoryUniversalInstantiation :: QuantModalRule lex (World -> Bool)
worldTheoryUniversalInstantiation = 
        [ GammaV 1 :|-: SS (lall "v" (phi 1))]
        ∴ GammaV 1 :|-: SS (phi 1 someWorld)

worldTheoryUniversalGeneralization :: QuantModalRule lex (World -> Bool)
worldTheoryUniversalGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 someWorld) ]
        ∴ GammaV 1 :|-: SS (lall "v" (phi 1))

worldTheoryExistentialGeneralization :: QuantModalRule lex (World -> Bool)
worldTheoryExistentialGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 someWorld)]
        ∴ GammaV 1 :|-: SS (lsome "v" (phi 1))

boxDerivation :: ModalRule lex b
boxDerivation = 
        [ GammaV 1 :|-: SS (phin 1 ./. someWorld) ]
        ∴ GammaV 1 :|-: SS (nec (phin 1) ./. someOtherWorld)

relativeBoxDerivation :: ModalRule lex b
relativeBoxDerivation = 
        [ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld)) ]
        ∴ GammaV 1 :|-: SS (nec (phin 1) ./. someWorld)

boxOut :: ModalRule lex b
boxOut = 
        [ GammaV 1 :|-: SS (nec (phin 1) ./. someWorld) ]
        ∴ GammaV 1 :|-: SS (phin 1 ./. someOtherWorld)

relativeBoxOut :: ModalRule lex b
relativeBoxOut = [ GammaV 1 :|-: SS (nec (phin 1) ./. someWorld) ]
                 ∴ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld))

reflexiveBoxOut :: ModalRule lex b
reflexiveBoxOut = [ GammaV 1 :|-: SS (nec (phin 1) ./. someWorld) ]
                  ∴ GammaV 1 :|-: SS (phin 1 ./. someWorld)

transitiveBoxOut :: ModalRule lex b
transitiveBoxOut = [ GammaV 1 :|-: SS (nec (phin 1) ./. someWorld) ]
                  ∴ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld `indexcons` someThirdWorld))

symmetricBoxOut :: ModalRule lex b
symmetricBoxOut = [ GammaV 1 :|-: SS (nec (phin 1) ./. (someWorld `indexcons` someOtherWorld)) ]
                  ∴ GammaV 1 :|-: SS (phin 1 ./. someWorld)

euclidianBoxOut :: ModalRule lex b
euclidianBoxOut = [ GammaV 1 :|-: SS (nec (phin 1) ./. (someWorld `indexcons` someOtherWorld)) ]
                  ∴ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someThirdWorld))

diamondOut :: ModalRule lex b
diamondOut = 
        [ GammaV 1 :|-: SS (pos (phin 1) ./. someWorld) ]
        ∴ GammaV 1 :|-: SS (phin 1 ./. someOtherWorld)

relativeDiamondOut :: ModalRule lex b
relativeDiamondOut =
        [ GammaV 1 :|-: SS (pos (phin 1) ./. someWorld) ]
        ∴ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld))

diamondIn :: ModalRule lex b
diamondIn = 
        [ GammaV 1 :|-: SS (phin 1 ./. someWorld) ]
        ∴ GammaV 1 :|-: SS (pos (phin 1) ./. someOtherWorld)

relativeDiamondIn :: ModalRule lex b
relativeDiamondIn = 
        [ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld)) ]
        ∴ GammaV 1 :|-: SS (pos (phin 1) ./. someWorld)

reflexiveDiamondIn :: ModalRule lex b
reflexiveDiamondIn = 
        [ GammaV 1 :|-: SS (phin 1 ./. someWorld) ]
        ∴ GammaV 1 :|-: SS (pos (phin 1) ./. someWorld)

transitiveDiamondIn :: ModalRule lex b
transitiveDiamondIn = 
        [ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld `indexcons` someThirdWorld)) ]
        ∴ GammaV 1 :|-: SS (pos (phin 1) ./. someWorld)

symmetricDiamondIn :: ModalRule lex b
symmetricDiamondIn = [ GammaV 1 :|-: SS (phin 1 ./. someWorld)]
                  ∴ GammaV 1 :|-: SS (pos (phin 1) ./. (someWorld `indexcons` someOtherWorld))

euclidianDiamondIn :: ModalRule lex b
euclidianDiamondIn = [ GammaV 1 :|-: SS (phin 1 ./. (someWorld `indexcons` someThirdWorld))]
                  ∴ GammaV 1 :|-: SS (pos (phin 1) ./. (someWorld `indexcons` someOtherWorld))

---------------------------
--  1.2 Variation Rules  --
---------------------------
type AbsoluteModalRuleVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , PrismCons (ClassicalSequentLexOver lex) World
        , ModalLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        ) => [SequentRule lex (Form b)]

type ModalRuleVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , PrismCons (ClassicalSequentLexOver lex) World
        , ModalLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexingLang (ClassicalSequentLexOver lex) (Term World) (Form b) (Form (World -> Bool))
        ) => [SequentRule lex (Form b)]

type QuantModalRuleVariants lex b = 
        ( Typeable b
        , QuantLanguage (ClassicalSequentOver lex (Form(World->Bool))) (ClassicalSequentOver lex (Term (World))) 
        , PolyadicSchematicPredicateLanguage (ClassicalSequentOver lex) (Term World) (Form (World -> Bool))
        , BooleanLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , PrismCons (ClassicalSequentLexOver lex) World
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , ModalLanguage (ClassicalSequentOver lex (Form (World -> Bool)))
        , IndexingLang (ClassicalSequentLexOver lex) (Term World) (Form b) (Form (World -> Bool))
        ) => [SequentRule lex (Form b)]

------------------------------
--  1.2.1 Simple Variation  --
------------------------------

-- Rules with several variations

worldlyExplicitConstructiveFalsumReductioVariations :: ModalRuleVariants lex b
worldlyExplicitConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (phin 1 ./. someWorld) :|-: SS (lfalsum ./. someOtherWorld)
                , SA ( phin 1 ./. someWorld) :|-: SS ( phin 1 ./. someWorld)
                ] ∴ GammaV 1 :|-: SS ((lneg $ phin 1) ./. someWorld)
            ,
                [ GammaV 1 :|-: SS (lfalsum ./. someOtherWorld)
                , SA (phin 1 ./. someWorld) :|-: SS (phin 1 ./. someWorld)
                ] ∴ GammaV 1 :|-: SS ((lneg $ phin 1) ./. someWorld)
            ]

worldlyExplicitNonConstructiveFalsumReductioVariations :: ModalRuleVariants lex b
worldlyExplicitNonConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA ((lneg $ phin 1) ./. someWorld) :|-: SS (lfalsum ./. someOtherWorld)
                , SA ((lneg $ phin 1) ./. someWorld) :|-: SS ((lneg $ phin 1) ./. someWorld)
                ] ∴ GammaV 1 :|-: SS ( phin 1 ./. someWorld)
            ,
                [ GammaV 1 :|-: SS (lfalsum ./. someOtherWorld)
                , SA ((lneg $ phin 1) ./. someWorld) :|-: SS ((lneg $ phin 1) ./. someWorld)
                ] ∴ GammaV 1 :|-: SS (phin 1 ./. someWorld)
            ]

worldTheoryExistentialDerivation :: QuantModalRuleVariants lex (World -> Bool)
worldTheoryExistentialDerivation = [
                                       [ GammaV 1 :+:  SA (phi 1 someWorld) :|-: SS (phin 1) 
                                       , GammaV 2 :|-: SS (lsome "v" $ phi 1)   
                                       , SA (phi 1 someWorld) :|-: SS (phi 1 someWorld)            
                                       ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)      
                                   ,
                                       [ GammaV 1 :|-: SS (phin 1)
                                       , SA (phi 1 someWorld) :|-: SS (phi 1 someWorld)
                                       , GammaV 2 :|-: SS (lsome "v" $ phi 1)
                                       ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
                                   ]

diamondDerivation :: ModalRuleVariants lex b
diamondDerivation = [
                        [ GammaV 1 :+:  SA (phin 1 ./. someWorld) :|-: SS (phin 2 ./. someThirdWorld) 
                        , GammaV 2 :|-: SS (pos (phin 1) ./. someOtherWorld)   
                        , SA (phin 1 ./. someWorld) :|-: SS (phin 1 ./. someWorld)            
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 ./. someThirdWorld)      
                    ,
                        [ GammaV 1 :|-: SS (phin 2 ./. someThirdWorld) 
                        , GammaV 2 :|-: SS (pos (phin 1) ./. someOtherWorld)   
                        , SA (phin 1 ./. someWorld) :|-: SS (phin 1 ./. someWorld)            
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 ./. someThirdWorld)      
                    ]

relativeDiamondDerivation :: ModalRuleVariants lex b
relativeDiamondDerivation = [
                                [ GammaV 1 :+:  SA (phin 1 ./. someWorld) :|-: SS (phin 2 ./. someThirdWorld) 
                                , GammaV 2 :|-: SS (pos (phin 1) ./. someWorld)   
                                , SA (phin 1 ./. (someWorld `indexcons` someOtherWorld)) :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld))
                                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 ./. someThirdWorld)
                            ,
                                [ GammaV 1 :|-: SS (phin 2 ./. someThirdWorld) 
                                , GammaV 2 :|-: SS (pos (phin 1) ./. someWorld)   
                                , SA (phin 1 ./. (someWorld `indexcons` someOtherWorld)) :|-: SS (phin 1 ./. (someWorld `indexcons` someOtherWorld))            
                                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 ./. someThirdWorld)      
                            ]

-----------------------------------
--  1.2.1.1 Bidirectional Rules  --
-----------------------------------

bidir x y = [[x] ∴ y, [y] ∴ x]

worldTheoryZeroAxiom :: ModalRuleVariants lex (World -> Bool)
worldTheoryZeroAxiom = bidir 
                ( GammaV 1 :|-: SS (phin 1) )
                ( GammaV 1 :|-: SS (phin 1 ./. world 0) )

worldTheoryNegAxiom :: ModalRuleVariants lex (World -> Bool)
worldTheoryNegAxiom = bidir
                ( GammaV 1 :|-: SS (lneg (phin 1) ./. someWorld) )
                ( GammaV 1 :|-: SS (lneg (phin 1 ./. someWorld)) )

worldTheoryAndAxiom :: ModalRuleVariants lex (World -> Bool)
worldTheoryAndAxiom = bidir
                ( GammaV 1 :|-: SS ((phin 1 .∧. phin 2) ./. someWorld) )
                ( GammaV 1 :|-: SS ((phin 1 ./. someWorld) .∧. (phin 2 ./. someWorld)) )

worldTheoryOrAxiom :: ModalRuleVariants lex (World -> Bool)
worldTheoryOrAxiom = bidir
                ( GammaV 1 :|-: SS ((phin 1 .∨. phin 2) ./. someWorld) )
                ( GammaV 1 :|-: SS ((phin 1 ./. someWorld) .∨. (phin 2 ./. someWorld)) )

worldTheoryIfAxiom :: ModalRuleVariants lex (World -> Bool)
worldTheoryIfAxiom = bidir
                ( GammaV 1 :|-: SS ((phin 1 .→. phin 2) ./. someWorld) )
                ( GammaV 1 :|-: SS ((phin 1 ./. someWorld) .→. (phin 2 ./. someWorld)) )

worldTheoryIffAxiom :: ModalRuleVariants lex (World -> Bool)
worldTheoryIffAxiom = bidir
                ( GammaV 1 :|-: SS ((phin 1 .↔. phin 2) ./. someWorld) )
                ( GammaV 1 :|-: SS ((phin 1 ./. someWorld) .↔. (phin 2 ./. someWorld)) )

worldTheoryAllAxiom :: QuantModalRuleVariants lex (World -> Bool)
worldTheoryAllAxiom = bidir
                ( GammaV 1 :|-: SS (lall "v" (\x -> phi 1 x ./. someWorld)))
                ( GammaV 1 :|-: SS (lall "v" (phi 1) ./. someWorld))

worldTheorySomeAxiom :: QuantModalRuleVariants lex (World -> Bool)
worldTheorySomeAxiom = bidir
                ( GammaV 1 :|-: SS (lsome "v" (\x -> phi 1 x ./. someWorld)))
                ( GammaV 1 :|-: SS (lsome "v" (phi 1) ./. someWorld))

worldTheoryNecAxiom :: QuantModalRuleVariants lex (World -> Bool)
worldTheoryNecAxiom = bidir
                ( GammaV 1 :|-: SS (lall "v" (\x -> phin 1 ./. x)))
                ( GammaV 1 :|-: SS ((nec $ phin 1) ./. someWorld ))

worldTheoryPosAxiom :: QuantModalRuleVariants lex (World -> Bool)
worldTheoryPosAxiom = bidir
                ( GammaV 1 :|-: SS (lsome "v" (\x -> phin 1 ./. x)))
                ( GammaV 1 :|-: SS ((pos $ phin 1) ./. someWorld ))

worldTheoryAtAxiom :: ModalRuleVariants lex (World -> Bool)
worldTheoryAtAxiom = bidir
                ( GammaV 1 :|-: SS (phin 1 ./. someWorld))
                ( GammaV 1 :|-: SS ((phin 1 ./. someWorld) ./. someOtherWorld))

quantifierNegation :: QuantModalRuleVariants lex (World -> Bool)
quantifierNegation = bidir ( GammaV 1 :|-: SS (lneg $ lall "v" (phi 1)))
                           ( GammaV 1 :|-: SS (lsome "v" (lneg . phi 1)))
                     ++ bidir ( GammaV 1 :|-: SS (lneg $ lsome "v" (phi 1)))
                              ( GammaV 1 :|-: SS (lall "v" (lneg . phi 1)))

modalNegation :: AbsoluteModalRuleVariants lex (World -> Bool)
modalNegation = bidir ( GammaV 1 :|-: SS ((pos $ lneg $ phin 1)))
                ( GammaV 1 :|-: SS ((lneg $ nec $ phin 1)))
                ++ bidir ( GammaV 1 :|-: SS ((nec $ lneg $ phin 1)))
                ( GammaV 1 :|-: SS ((lneg $ pos $ phin 1)))

----------------------------------------
--  1.2.3 Infinitary Variation Rules  --
----------------------------------------

-- rules with an infnite number of schematic variations
