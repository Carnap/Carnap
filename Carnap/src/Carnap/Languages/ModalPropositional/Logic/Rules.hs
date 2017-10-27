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
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.ModalPropositional.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules
import Data.Typeable
import Data.List (intercalate)

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

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

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

instance Eq (WorldTheorySequentCalc a) where
        (==) = (=*)

instance ParsableLex (Form (World -> Bool)) WorldTheoryPropLexicon where
        langParser = worldTheoryPropFormulaParser

instance ParsableLex (Form Bool) AbsoluteModalPropLexicon where
        langParser = absoluteModalPropFormulaParser

instance ParsableLex (Form (World -> Bool)) AbsoluteModalPropLexicon where
        langParser = absoluteModalPropFormulaPreParser

instance PrismBooleanConnLex CoreCalcLex (World -> Bool)
instance PrismPropositionalContext CoreCalcLex (World -> Bool)
instance PrismBooleanConst CoreCalcLex (World -> Bool)
instance PrismPropLex CoreCalcLex (World -> Bool)
instance PrismSchematicProp CoreCalcLex (World -> Bool)
instance PrismModality CoreCalcLex (World -> Bool)

instance PrismBooleanConnLex WorldTheorySequentCalcLex (World -> Bool)
instance PrismPropositionalContext WorldTheorySequentCalcLex (World -> Bool)
instance PrismBooleanConst WorldTheorySequentCalcLex (World -> Bool)
instance PrismPropLex WorldTheorySequentCalcLex (World -> Bool)
instance PrismSchematicProp WorldTheorySequentCalcLex (World -> Bool)
instance PrismModality WorldTheorySequentCalcLex (World -> Bool)

instance PrismBooleanConnLex AbsoluteModalPropSequentCalcLex Bool
instance PrismPropositionalContext AbsoluteModalPropSequentCalcLex Bool
instance PrismBooleanConst AbsoluteModalPropSequentCalcLex Bool
instance PrismPropLex AbsoluteModalPropSequentCalcLex Bool
instance PrismSchematicProp AbsoluteModalPropSequentCalcLex Bool
instance PrismModality AbsoluteModalPropSequentCalcLex Bool

instance PrismBooleanConnLex AbsoluteModalPropSequentCalcLex (World -> Bool)
instance PrismPropositionalContext AbsoluteModalPropSequentCalcLex (World -> Bool)
instance PrismBooleanConst AbsoluteModalPropSequentCalcLex (World -> Bool)
instance PrismPropLex AbsoluteModalPropSequentCalcLex (World -> Bool)
instance PrismSchematicProp AbsoluteModalPropSequentCalcLex (World -> Bool)
instance PrismModality AbsoluteModalPropSequentCalcLex (World -> Bool)

phi :: Int -> WorldTheorySequentCalc (Term World) -> WorldTheorySequentCalc (Form (World -> Bool))
phi n x = SeqPPhi n :!$: x

wtlgamma :: Int -> WorldTheorySequentCalc (Antecedent (Form (World -> Bool)))
wtlgamma = GammaV

absgamma :: Int -> AbsoluteModalPropSequentCalc (Antecedent (Form Bool))
absgamma = GammaV

someWorld = worldScheme 0 

someOtherWorld = worldScheme 1 

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

type ModalRule lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        , ModalLanguage (ClassicalSequentOver lex (Form b))
        , IndexingLang lex (Term World) (Form b) (Form (World -> Bool))
        ) => SequentRule lex (Form b)
--Rules found in many systems of propositional logic

worldlyFalsumElimination :: ModalRule lex b
worldlyFalsumElimination = [ GammaV 1 :|-: SS (lfalsum :/: SomeWorld)
                           ] ∴ GammaV 1 :|-: SS (phin 1 :/: SomeOtherWorld)

worldlyFalsumIntroduction :: ModalRule lex b
worldlyFalsumIntroduction = [ GammaV 1 :|-: SS ((lneg $ phin 1) :/: SomeWorld)
                            , GammaV 2 :|-: SS (phin 1 :/: SomeWorld)
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lfalsum :/: SomeOtherWorld)

worldTheoryUniversalInstantiation :: ModalRule lex b
worldTheoryUniversalInstantiation = 
        [ GammaV 1 :|-: SS (SeqBind (All "v") (phi 1))]
        ∴ GammaV 1 :|-: SS (phi 1 SomeWorld)

worldTheoryUniversalGeneralization :: ModalRule lex b
worldTheoryUniversalGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqBind (All "v") (phi 1))

worldTheoryExistentialGeneralization :: ModalRule lex b
worldTheoryExistentialGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 SomeWorld)]
        ∴ GammaV 1 :|-: SS (SeqBind (Some "v") (phi 1))

boxDerivation :: ModalRule lex b
boxDerivation = 
        [ GammaV 1 :|-: SS (phin 1 :/: SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqNec (phin 1) :/: SomeOtherWorld)

boxOut :: ModalRule lex b
boxOut = 
        [ GammaV 1 :|-: SS (SeqNec (phin 1) :/: SomeWorld) ]
        ∴ GammaV 1 :|-: SS (phin 1 :/: SomeOtherWorld)

diamondIn :: ModalRule lex b
diamondIn = 
        [ GammaV 1 :|-: SS (phin 1 :/: SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqPos (phin 1) :/: SomeOtherWorld)

---------------------------
--  1.2 Variation Rules  --
---------------------------

type ModalRuleVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        , ModalLanguage (ClassicalSequentOver lex (Form b))
        ) => [SequentRule lex (Form b)]

------------------------------
--  1.2.1 Simple Variation  --
------------------------------

-- Rules with several variations

worldlyExplicitConstructiveFalsumReductioVariations :: ModalRuleVariants lex b
worldlyExplicitConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (phin 1 :/: SomeWorld) :|-: SS (lfalsum :/: SomeOtherWorld)
                , SA ( phin 1 :/: SomeWorld) :|-: SS ( phin 1 :/: SomeWorld)
                ] ∴ GammaV 1 :|-: SS ((lneg $ phin 1) :/: SomeWorld)
            ,
                [ GammaV 1 :|-: SS (lfalsum :/: SomeOtherWorld)
                , SA (phin 1 :/: SomeWorld) :|-: SS (phin 1 :/: SomeWorld)
                ] ∴ GammaV 1 :|-: SS ((lneg $ phin 1) :/: SomeWorld)
            ]

worldlyExplicitNonConstructiveFalsumReductioVariations :: ModalRuleVariants lex b
worldlyExplicitNonConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA ((lneg $ phin 1) :/: SomeWorld) :|-: SS (lfalsum :/: SomeOtherWorld)
                , SA ((lneg $ phin 1) :/: SomeWorld) :|-: SS ((lneg $ phin 1) :/: SomeWorld)
                ] ∴ GammaV 1 :|-: SS ( phin 1 :/: SomeWorld)
            ,
                [ GammaV 1 :|-: SS (lfalsum :/: SomeOtherWorld)
                , SA ((lneg $ phin 1) :/: SomeWorld) :|-: SS ((lneg $ phin 1) :/: SomeWorld)
                ] ∴ GammaV 1 :|-: SS (phin 1 :/: SomeWorld)
            ]

worldTheoryExistentialDerivation :: ModalRuleVariants lex b
worldTheoryExistentialDerivation = [
                                       [ GammaV 1 :+:  SA (phi 1 SomeWorld) :|-: SS (SeqPhi 1) 
                                       , GammaV 2 :|-: SS (SeqBind (Some "v") $ phi 1)   
                                       , SA (phi 1 SomeWorld) :|-: SS (phi 1 SomeWorld)            
                                       ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)      
                                   ,
                                       [ GammaV 1 :|-: SS (SeqPhi 1)
                                       , SA (phi 1 SomeWorld) :|-: SS (phi 1 SomeWorld)
                                       , GammaV 2 :|-: SS (SeqBind (Some "v") $ phi 1)
                                       ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
                                   ]

diamondDerivation :: ModalRuleVariants lex b
diamondDerivation = [
                        [ GammaV 1 :+:  SA (phin 1 :/: SomeWorld) :|-: SS (phin 2 :/: SomeThirdWorld) 
                        , GammaV 2 :|-: SS (SeqPos (phin 1) :/: SomeOtherWorld)   
                        , SA (phin 1 :/: SomeWorld) :|-: SS (phin 1 :/: SomeWorld)            
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 :/: SomeThirdWorld)      
                    ,
                        [ GammaV 1 :|-: SS (phin 2 :/: SomeThirdWorld) 
                        , GammaV 2 :|-: SS (SeqPos (phin 1) :/: SomeOtherWorld)   
                        , SA (phin 1 :/: SomeWorld) :|-: SS (phin 1 :/: SomeWorld)            
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 :/: SomeThirdWorld)      
                    ]

-----------------------------------
--  1.2.1.1 Bidirectional Rules  --
-----------------------------------

bidir x y = [[x] ∴ y, [y] ∴ x]

worldTheoryZeroAxiom :: ModalRuleVariants lex b
worldTheoryZeroAxiom = bidir 
                ( GammaV 1 :|-: SS (SeqPhi 1) )
                ( GammaV 1 :|-: SS (SeqPhi 1 :/: TheWorld) )

worldTheoryNegAxiom :: ModalRuleVariants lex b
worldTheoryNegAxiom = bidir
                ( GammaV 1 :|-: SS (lneg (SeqPhi 1) :/: SomeWorld) )
                ( GammaV 1 :|-: SS (lneg (SeqPhi 1 :/: SomeWorld)) )

worldTheoryAndAxiom :: ModalRuleVariants lex b
worldTheoryAndAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :&-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :&-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryOrAxiom :: ModalRuleVariants lex b
worldTheoryOrAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :||-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :||-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryIfAxiom :: ModalRuleVariants lex b
worldTheoryIfAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :->-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :->-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryIffAxiom :: ModalRuleVariants lex b
worldTheoryIffAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :<->-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :<->-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryAllAxiom :: ModalRuleVariants lex b
worldTheoryAllAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (All "v") (\x -> phi 1 x :/: SomeWorld)))
                ( GammaV 1 :|-: SS (SeqBind (All "v") (phi 1) :/: SomeWorld))

worldTheorySomeAxiom :: ModalRuleVariants lex b
worldTheorySomeAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (Some "v") (\x -> phi 1 x :/: SomeWorld)))
                ( GammaV 1 :|-: SS (SeqBind (Some "v") (phi 1) :/: SomeWorld))

worldTheoryNecAxiom :: ModalRuleVariants lex b
worldTheoryNecAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (All "v") (\x -> SeqPhi 1 :/: x)))
                ( GammaV 1 :|-: SS ((SeqNec $ SeqPhi 1) :/: SomeWorld ))

worldTheoryPosAxiom :: ModalRuleVariants lex b
worldTheoryPosAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (Some "v") (\x -> SeqPhi 1 :/: x)))
                ( GammaV 1 :|-: SS ((SeqPos $ SeqPhi 1) :/: SomeWorld ))

worldTheoryAtAxiom :: ModalRuleVariants lex b
worldTheoryAtAxiom = bidir
                ( GammaV 1 :|-: SS (SeqPhi 1 :/: SomeWorld))
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :/: SeqSchmIdx 1))

quantifierNegation :: ModalRuleVariants lex b
quantifierNegation = bidir ( GammaV 1 :|-: SS (lneg $ SeqBind (All "v") (phi 1)))
                           ( GammaV 1 :|-: SS (SeqBind (Some "v") (lneg . phi 1)))
                     ++ bidir ( GammaV 1 :|-: SS (lneg $ SeqBind (Some "v") (phi 1)))
                              ( GammaV 1 :|-: SS (SeqBind (All "v") (lneg . phi 1)))

modalNegation :: ModalRuleVariants lex b
modalNegation = bidir ( GammaV 1 :|-: SS ((pos $ lneg $ phin 1)))
                ( GammaV 1 :|-: SS ((lneg $ nec $ phin 1)))
                ++ bidir ( GammaV 1 :|-: SS ((nec $ lneg $ phin 1)))
                ( GammaV 1 :|-: SS ((lneg $ pos $ phin 1)))

----------------------------------------
--  1.2.3 Infinitary Variation Rules  --
----------------------------------------

-- rules with an infnite number of schematic variations
