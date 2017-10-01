{-#LANGUAGE GADTs, PatternSynonyms, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeOperators #-}
module Carnap.Languages.ModalPropositional.Logic.Rules where

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
import Data.Typeable
import Data.List (intercalate)

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type WorldTheorySequentCalc = ClassicalSequentOver WorldTheoryPropLexicon

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

pattern SeqP x arity      = FX (Lx2 (Lx1 (Lx1 (Predicate x arity))))
pattern SeqSP x arity     = FX (Lx2 (Lx1 (Lx2 (Predicate x arity))))
pattern SeqCon x arity    = FX (Lx2 (Lx1 (Lx3 (Connective x arity))))
pattern SeqBox            = FX (Lx2 (Lx1 (Lx4 (Connective Box AOne))))
pattern SeqDia            = FX (Lx2 (Lx1 (Lx4 (Connective Diamond AOne))))
pattern SeqIndexer        = FX (Lx2 (Lx2 (Lx1 AtIndex)))
pattern SeqIndicies c a   = FX (Lx2 (Lx2 (Lx2 (Function c a))))
pattern SeqIdxCons c a    = FX (Lx2 (Lx2 (Lx3 (Function c a))))
pattern SeqQuant q        = FX (Lx2 (Lx2 (Lx4 (Bind q))))
pattern SeqSchemIdx c a   = FX (Lx2 (Lx2 (Lx5 (Function c a))))
pattern SeqSchemPred c a  = FX (Lx2 (Lx2 (Lx6 (Predicate c a))))
pattern LFalsum           = FX (Lx2 (Lx1 (Lx5 (Connective Falsum AZero))))
pattern SeqSV n           = FX (Lx2 (Lx1 (Lx6 (StaticVar n))))
pattern SeqProp n         = SeqP (Prop n) AZero
pattern SeqPhi :: Int -> WorldTheorySequentCalc (Form (World -> Bool))
pattern SeqPhi n          = SeqSP (SProp n) AZero
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

phi :: Int -> WorldTheorySequentCalc (Term World) -> WorldTheorySequentCalc (Form (World -> Bool))
phi n x = SeqPPhi n :!$: x

wtlgamma :: Int -> WorldTheorySequentCalc (Antecedent (Form (World -> Bool)))
wtlgamma = GammaV

worldTheorySeqParser = seqFormulaParser :: Parsec String u (WorldTheorySequentCalc (Sequent (Form (World -> Bool))))

-------------------------
--  1.1 Standard Rules  --
-------------------------
--Rules found in many systems of propositional logic

modusPonens = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
              , GammaV 2 :|-: SS (SeqPhi 1)
              ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)

modusTollens = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
               , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
               ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)

axiom = [] ∴ SA (SeqPhi 1) :|-: SS (SeqPhi 1)

identityRule = [ GammaV 1 :|-: SS (SeqPhi 1) 
               ] ∴ GammaV 1 :|-: SS (SeqPhi 1)

doubleNegationElimination = [ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) 
                            ] ∴ GammaV 1 :|-: SS (SeqPhi 1) 

doubleNegationIntroduction = [ GammaV 1 :|-: SS (SeqPhi 1) 
                             ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) 

falsumElimination = [ GammaV 1 :|-: SS LFalsum
                    ] ∴ GammaV 1 :|-: SS (SeqPhi 1)

falsumIntroduction = [ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1)
                     , GammaV 2 :|-: SS (SeqPhi 1)
                     ] ∴ GammaV 1 :+: GammaV 2 :|-: SS LFalsum

adjunction = [ GammaV 1  :|-: SS (SeqPhi 1) 
             , GammaV 2  :|-: SS (SeqPhi 2)
             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1 :&-: SeqPhi 2)

conditionalToBiconditional = [ GammaV 1  :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                             , GammaV 2  :|-: SS (SeqPhi 2 :->-: SeqPhi 1) 
                             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)

dilemma = [ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
          , GammaV 2 :|-: SS (SeqPhi 1 :->-: SeqPhi 3)
          , GammaV 3 :|-: SS (SeqPhi 2 :->-: SeqPhi 3)
          ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)

hypotheticalSyllogism = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                        , GammaV 2 :|-: SS (SeqPhi 2 :->-: SeqPhi 3)
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1 :->-: SeqPhi 3)

worldTheoryUniversalInstantiation = 
        [ GammaV 1 :|-: SS (SeqBind (All "v") (phi 1))]
        ∴ GammaV 1 :|-: SS (phi 1 SomeWorld)

worldTheoryUniversalGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 SomeWorld) ]
        ∴ GammaV 1 :|-: SS (SeqBind (All "v") (phi 1))

worldTheoryExistentialGeneralization = 
        [ GammaV 1 :|-: SS (phi 1 SomeWorld)]
        ∴ GammaV 1 :|-: SS (SeqBind (Some "v") (phi 1))

---------------------------
--  1.2 Variation Rules  --
---------------------------

------------------------------
--  1.2.1 Simple Variation  --
------------------------------

-- Rules with several variations

modusTollendoPonensVariations = [
                [ GammaV 1  :|-: SS (SeqNeg $ SeqPhi 1) 
                , GammaV 2  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            , 
                [ GammaV 1  :|-: SS (SeqNeg $ SeqPhi 1) 
                , GammaV 2  :|-: SS (SeqPhi 2 :||-: SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ]

constructiveReductioVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,

                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,

                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ]

explicitConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS LFalsum
                , SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1)
            ,
                [ GammaV 1 :|-: SS LFalsum
                , SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1)
            ]

explicitNonConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS LFalsum
                , SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 1)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1)
            ,
                [ GammaV 1 :|-: SS LFalsum
                , SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 1)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1)
            ]

nonConstructiveReductioVariations = [
                [ GammaV 1 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ,

                [ GammaV 1 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ,

                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( SeqPhi 1)
            ]

conditionalProofVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2) 
            ,   [ GammaV 1 :|-: SS (SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
            ]

explicitConditionalProofVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1)  :|-: SS (SeqPhi 2) 
                , SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2) 
            ,   [ GammaV 1 :|-: SS (SeqPhi 2) 
                , SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
            ]

simplificationVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :&-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1 :&-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 2)
            ]

additionVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :||-: SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
            ]

biconditionalToConditionalVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :->-: SeqPhi 1)
            , 
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
            ]

proofByCasesVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 3)
                , GammaV 3 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ,   
                [ GammaV 1  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 3)
                , GammaV 3 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ,   
                [ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 3)
                , GammaV 3 :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            , 
                [ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 3)
                , GammaV 3 :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ]

tertiumNonDaturVariations = [
                [ SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                , SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 1)
                , GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ,   
                [ SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                , SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 1)
                , GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ,   
                [ SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                , SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 1)
                , GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            , 
                [ SA (SeqPhi 1) :|-: SS (SeqPhi 1)
                , SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 1)
                , GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ]

biconditionalProofVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ,
                [ GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ,
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            , 
                [ GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ]

biconditionalPonensVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)
                , GammaV 2  :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)
                , GammaV 2  :|-: SS (SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ]

materialConditionalVariations =  [
                [ GammaV 1 :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :->-: SeqPhi 1)
            ,
                [ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :->-: SeqPhi 1)
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

-----------------------------------
--  1.2.1.1 Bidirectional Rules  --
-----------------------------------

bidir x y = [[x] ∴ y, [y] ∴ x]

deMorgansNegatedOr = bidir 
                ( GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :||-: SeqPhi 2) )
                ( GammaV 1 :|-: SS (SeqNeg (SeqPhi 1) :&-: SeqNeg (SeqPhi 2)) )

negatedBiconditionalVariations = bidir
                ( GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :<->-: SeqPhi 2) )
                ( GammaV 1 :|-: SS (SeqNeg (SeqPhi 1) :<->-: SeqPhi 2) )

negatedConjunctionVariations = bidir
                ( GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :&-: SeqPhi 2) )
                ( GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqNeg (SeqPhi 2)) )

negatedConditionalVariations = bidir
                ( GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :->-: SeqPhi 2) )
                ( GammaV 1 :|-: SS (SeqPhi 1 :&-: SeqNeg (SeqPhi 2)) )

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

-------------------------------
--  1.2.2 Replacement Rules  --
-------------------------------

-- replace :: WorldTheoryPropLanguage (Form (World -> Bool)) -> WorldTheoryPropLanguage (Form (World -> Bool)) -> [SequentRule (CoreLexicon :|: WorldTheoryLexicon)]
-- replace x y = [ [GammaV 1  :|-: ss (propCtx 1 x)] ∴ GammaV 1  :|-: ss (propCtx 1 y)
--               , [GammaV 1  :|-: ss (propCtx 1 y)] ∴ GammaV 1  :|-: ss (propCtx 1 x)]
--     where ss = SS . liftToSequent

-- andCommutativity = replace (phin 1 ./\. phin 2) (phin 2 ./\. phin 1)

-- orCommutativity = replace (phin 1 .\/. phin 2) (phin 2 .\/. phin 1)

-- iffCommutativity = replace (phin 1 .<=>. phin 2) (phin 2 .<=>. phin 1)

-- deMorgansLaws = replace (lneg $ phin 1 ./\. phin 2) (lneg (phin 1) .\/. lneg (phin 2))
--              ++ replace (lneg $ phin 1 .\/. phin 2) (lneg (phin 1) ./\. lneg (phin 2))

-- doubleNegation = replace (lneg $ lneg $ phin 1) (phin 1)

-- materialConditional = replace (phin 1 .=>. phin 2) (lneg (phin 1) .\/. phin 2)
--                    ++ replace (phin 1 .\/. phin 2) (lneg (phin 1) .=>. phin 2)

-- biconditionalExchange = replace (phin 1 .<=>. phin 2) ((phin 1 .=>. phin 2) ./\. (phin 2 .=>. phin 1))

----------------------------------------
--  1.2.3 Infinitary Variation Rules  --
----------------------------------------

-- rules with an infnite number of schematic variations

-- XXX at the moment, these requires all assumptions to be used. Should
-- actually be parameterized by l::[Bool] of length n rather than n::Int
-- or alternately, the checking mechanism should be modified to allow
-- weakening.

eliminationOfCases n = (premAnt n :|-: SS LFalsum
                     : take n (map premiseForm [1 ..]))
                     ∴ GammaV 1 :|-: SS (concSuc n)
    where premiseForm m = SA (SeqNeg $ SeqPhi m) :|-: SS (SeqNeg $ SeqPhi m)
          premAnt m = foldr (:+:) (GammaV 1) (take m $ map (SA . SeqNeg . SeqPhi) [1 ..])
          concSuc m = foldr (:||-:) (SeqPhi 1) (take (m - 1) $ map SeqPhi [2 ..])

-- XXX slight variation from Hardegree's rule, which has weird ad-hoc syntax.
separationOfCases n = (GammaV 0 :|-: SS (premSuc n)
                    : take n (map premiseForm [1 ..]))
                    ∴ concAnt n :|-: SS (SeqPhi 0)
    where premSuc m = foldr (:||-:) (SeqPhi 1) (take (m - 1) $ map SeqPhi [2 ..])
          premiseForm m = GammaV m :+: SA (SeqPhi m) :|-: SS (SeqPhi 0)
          concAnt m = foldr (:+:) (GammaV 0) (take m $ map GammaV [1 ..])
