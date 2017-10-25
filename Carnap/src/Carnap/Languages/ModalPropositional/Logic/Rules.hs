{-#LANGUAGE GADTs, PatternSynonyms, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeOperators #-}
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
pattern SeqAbsIndexer     = FX (Lx2 (Lx2 (Lx1 AtAbsIndex)))
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
pattern (://:) x y        = SeqAbsIndexer :!$: x :!$: y
pattern SeqNeg x          = SeqNot :!$: x
pattern SeqBind q f       = SeqQuant q :!$: LLam f
pattern SeqIndex n        = SeqIndicies (Index n) AZero
pattern SeqSchmIdx n      = SeqSchemIdx (SFunc AZero n) AZero
pattern TheWorld          = SeqIndex 0
pattern SomeWorld         = SeqSchmIdx 0
pattern SomeOtherWorld    = SeqSchmIdx 1
pattern SomeThirdWorld    = SeqSchmIdx 2
pattern SeqCons x y       = SeqIdxCons IndexCons ATwo :!$: x :!$: y

eigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The index " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The index " ++ show c' ++ " appears not to be fresh in the other premise " ++ show suc'
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

instance PrismBooleanConnLex WorldTheorySequentCalcLex (World -> Bool)
instance PrismPropositionalContext WorldTheorySequentCalcLex (World -> Bool)
instance PrismBooleanConst WorldTheorySequentCalcLex (World -> Bool)
instance PrismPropLex WorldTheorySequentCalcLex (World -> Bool)
instance PrismSchematicProp WorldTheorySequentCalcLex (World -> Bool)

instance PrismBooleanConnLex AbsoluteModalPropSequentCalcLex Bool
instance PrismPropositionalContext AbsoluteModalPropSequentCalcLex Bool
instance PrismBooleanConst AbsoluteModalPropSequentCalcLex Bool
instance PrismPropLex AbsoluteModalPropSequentCalcLex Bool
instance PrismSchematicProp AbsoluteModalPropSequentCalcLex Bool

phi :: Int -> WorldTheorySequentCalc (Term World) -> WorldTheorySequentCalc (Form (World -> Bool))
phi n x = SeqPPhi n :!$: x

wtlgamma :: Int -> WorldTheorySequentCalc (Antecedent (Form (World -> Bool)))
wtlgamma = GammaV

absgamma :: Int -> AbsoluteModalPropSequentCalc (Antecedent (Form (World -> Bool)))
absgamma = GammaV

worldTheorySeqParser = seqFormulaParser :: Parsec String u (WorldTheorySequentCalc (Sequent (Form (World -> Bool))))

absoluteModalPropSeqParser = liftAbsSeq TheWorld <$> (seqFormulaParser :: Parsec String u (WorldTheorySequentCalc (Sequent (Form (World -> Bool)))))

liftAbsRule (SequentRule p c) = map (liftAbsSeq SomeWorld) p ∴ liftAbsSeq SomeWorld c

liftAbsSeq :: AbsoluteModalPropSequentCalc (Term World) -> WorldTheorySequentCalc (Sequent (Form (World -> Bool))) -> AbsoluteModalPropSequentCalc (Sequent (Form Bool))
liftAbsSeq w (a :|-: s) = atSomeAnt a :|-: atSomeSuc s
    where 
          atSomeAnt :: WorldTheorySequentCalc (Antecedent (Form (World -> Bool))) -> AbsoluteModalPropSequentCalc (Antecedent (Form Bool))
          atSomeAnt (x :+: y) = atSomeAnt x :+: atSomeAnt y
          atSomeAnt (SA x) = SA (reconstruct x ://: w) 
          atSomeAnt (GammaV n) = GammaV n
          atSomeAnt Top        = Top

          atSomeSuc :: WorldTheorySequentCalc (Succedent (Form (World -> Bool))) -> AbsoluteModalPropSequentCalc (Succedent (Form Bool))
          atSomeSuc (x :-: y) = atSomeSuc x :-: atSomeSuc y
          atSomeSuc (SS x) = SS (reconstruct x ://: w) 
          atSomeSuc Bot = Bot
          reconstruct (x:&-:y) = reconstruct x :&-: reconstruct y
          reconstruct (x:||-:y) = reconstruct x :||-: reconstruct y
          reconstruct (x:->-:y) = reconstruct x :->-: reconstruct y
          reconstruct (x:<->-:y) = reconstruct x :<->-: reconstruct y
          reconstruct (SeqNec x) = SeqNec $ reconstruct x
          reconstruct (SeqPos x) = SeqPos $ reconstruct x
          reconstruct (SeqNeg x) = SeqNeg $ reconstruct x
          reconstruct (SeqPhi n) = SeqPhiA n
          reconstruct (SeqProp n) = SeqProp n
          reconstruct LFalsum = LFalsum
          reconstruct LVerum = LVerum
          reconstruct x = error $ "cannot reconstruct " ++ show x ++ " from wtl to l"

-------------------------
--  1.1 Standard Rules  --
-------------------------
--Rules found in many systems of propositional logic

worldlyFalsumElimination = [ GammaV 1 :|-: SS (LFalsum ://: SomeWorld)
                           ] ∴ GammaV 1 :|-: SS (SeqPhiA 1 ://: SomeOtherWorld)

worldlyFalsumIntroduction = [ GammaV 1 :|-: SS ((SeqNeg $ SeqPhiA 1) ://: SomeWorld)
                            , GammaV 2 :|-: SS (SeqPhiA 1 ://: SomeWorld)
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (LFalsum ://: SomeOtherWorld)

worldTheoryUniversalInstantiation = 
        [ GammaV 1 :|-: SS (SeqBind (All "v") (phi 1))]
        ∴ GammaV 1 :|-: SS (phi 1 SomeWorld)

worldTheoryUniversalGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqBind (All "v") (phi 1))

boxDerivation = 
        [ GammaV 1 :|-: SS (SeqPhiA 1 ://: SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqNec (SeqPhiA 1) ://: SomeOtherWorld)

boxOut = 
        [ GammaV 1 :|-: SS (SeqNec (SeqPhiA 1) ://: SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqPhiA 1 ://: SomeOtherWorld)

worldTheoryExistentialGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 SomeWorld)]
        ∴ GammaV 1 :|-: SS (SeqBind (Some "v") (phi 1))

diamondIn = 
        [ GammaV 1 :|-: SS (SeqPhiA 1 ://: SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqPos (SeqPhiA 1) ://: SomeOtherWorld)

---------------------------
--  1.2 Variation Rules  --
---------------------------

------------------------------
--  1.2.1 Simple Variation  --
------------------------------

-- Rules with several variations

worldlyExplicitConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (SeqPhiA 1 ://: SomeWorld) :|-: SS (LFalsum ://: SomeOtherWorld)
                , SA ( SeqPhiA 1 ://: SomeWorld) :|-: SS ( SeqPhiA 1 ://: SomeWorld)
                ] ∴ GammaV 1 :|-: SS ((SeqNeg $ SeqPhiA 1) ://: SomeWorld)
            ,
                [ GammaV 1 :|-: SS (LFalsum ://: SomeOtherWorld)
                , SA (SeqPhiA 1 ://: SomeWorld) :|-: SS (SeqPhiA 1 ://: SomeWorld)
                ] ∴ GammaV 1 :|-: SS ((SeqNeg $ SeqPhiA 1) ://: SomeWorld)
            ]

worldlyExplicitNonConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA ((SeqNeg $ SeqPhiA 1) ://: SomeWorld) :|-: SS (LFalsum ://: SomeOtherWorld)
                , SA ((SeqNeg $ SeqPhiA 1) ://: SomeWorld) :|-: SS ((SeqNeg $ SeqPhiA 1) ://: SomeWorld)
                ] ∴ GammaV 1 :|-: SS ( SeqPhiA 1 ://: SomeWorld)
            ,
                [ GammaV 1 :|-: SS (LFalsum ://: SomeOtherWorld)
                , SA ((SeqNeg $ SeqPhiA 1) ://: SomeWorld) :|-: SS ((SeqNeg $ SeqPhiA 1) ://: SomeWorld)
                ] ∴ GammaV 1 :|-: SS (SeqPhiA 1 ://: SomeWorld)
            ]

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

diamondDerivation = [
                        [ GammaV 1 :+:  SA (SeqPhiA 1 ://: SomeWorld) :|-: SS (SeqPhiA 2 ://: SomeThirdWorld) 
                        , GammaV 2 :|-: SS (SeqPos (SeqPhiA 1) ://: SomeOtherWorld)   
                        , SA (SeqPhiA 1 ://: SomeWorld) :|-: SS (SeqPhiA 1 ://: SomeWorld)            
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhiA 2 ://: SomeThirdWorld)      
                    ,
                        [ GammaV 1 :|-: SS (SeqPhiA 2 ://: SomeThirdWorld) 
                        , GammaV 2 :|-: SS (SeqPos (SeqPhiA 1) ://: SomeOtherWorld)   
                        , SA (SeqPhiA 1 ://: SomeWorld) :|-: SS (SeqPhiA 1 ://: SomeWorld)            
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhiA 2 ://: SomeThirdWorld)      
                    ]

-----------------------------------
--  1.2.1.1 Bidirectional Rules  --
-----------------------------------

bidir x y = [[x] ∴ y, [y] ∴ x]

worldTheoryZeroAxiom = bidir 
                ( GammaV 1 :|-: SS (SeqPhi 1) )
                ( GammaV 1 :|-: SS (SeqPhi 1 :/: TheWorld) )

worldTheoryNegAxiom = bidir
                ( GammaV 1 :|-: SS (SeqNeg (SeqPhi 1) :/: SomeWorld) )
                ( GammaV 1 :|-: SS (SeqNeg (SeqPhi 1 :/: SomeWorld)) )

worldTheoryAndAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :&-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :&-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryOrAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :||-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :||-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryIfAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :->-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :->-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryIffAxiom = bidir
                ( GammaV 1 :|-: SS ((SeqPhi 1 :<->-: SeqPhi 2) :/: SomeWorld) )
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :<->-: (SeqPhi 2 :/: SomeWorld)) )

worldTheoryAllAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (All "v") (\x -> phi 1 x :/: SomeWorld)))
                ( GammaV 1 :|-: SS (SeqBind (All "v") (phi 1) :/: SomeWorld))

worldTheorySomeAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (Some "v") (\x -> phi 1 x :/: SomeWorld)))
                ( GammaV 1 :|-: SS (SeqBind (Some "v") (phi 1) :/: SomeWorld))

worldTheoryNecAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (All "v") (\x -> SeqPhi 1 :/: x)))
                ( GammaV 1 :|-: SS ((SeqNec $ SeqPhi 1) :/: SomeWorld ))

worldTheoryPosAxiom = bidir
                ( GammaV 1 :|-: SS (SeqBind (Some "v") (\x -> SeqPhi 1 :/: x)))
                ( GammaV 1 :|-: SS ((SeqPos $ SeqPhi 1) :/: SomeWorld ))

worldTheoryAtAxiom = bidir
                ( GammaV 1 :|-: SS (SeqPhi 1 :/: SomeWorld))
                ( GammaV 1 :|-: SS ((SeqPhi 1 :/: SomeWorld) :/: SeqSchmIdx 1))

quantifierNegation = bidir ( GammaV 1 :|-: SS (SeqNeg $ SeqBind (All "v") (phi 1)))
                           ( GammaV 1 :|-: SS (SeqBind (Some "v") (SeqNeg . phi 1)))
                     ++ bidir ( GammaV 1 :|-: SS (SeqNeg $ SeqBind (Some "v") (phi 1)))
                              ( GammaV 1 :|-: SS (SeqBind (All "v") (SeqNeg . phi 1)))

modalNegation = bidir ( GammaV 1 :|-: SS ((SeqPos $ SeqNeg $ SeqPhi 1)))
                ( GammaV 1 :|-: SS ((SeqNeg $ SeqNec $ SeqPhi 1)))
                ++ bidir ( GammaV 1 :|-: SS ((SeqNec $ SeqNeg $ SeqPhi 1)))
                ( GammaV 1 :|-: SS ((SeqNeg $ SeqPos $ SeqPhi 1)))

----------------------------------------
--  1.2.3 Infinitary Variation Rules  --
----------------------------------------

-- rules with an infnite number of schematic variations
