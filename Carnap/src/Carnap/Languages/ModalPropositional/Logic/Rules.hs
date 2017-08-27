{-#LANGUAGE GADTs, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses, TypeOperators #-}
module Carnap.Languages.ModalPropositional.Logic.Rules where

import Text.Parsec
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.ModalPropositional.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConnectives
import Data.Typeable

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type WorldTheorySequentCalc = ClassicalSequentOver (CoreLexicon :|: WorldTheoryLexicon)

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema WorldTheorySequentCalc

pattern SeqP x arity      = FX (Lx2 (Lx1 (Lx1 (Predicate x arity))))
pattern SeqSP x arity     = FX (Lx2 (Lx1 (Lx2 (Predicate x arity))))
pattern SeqCon x arity    = FX (Lx2 (Lx1 (Lx3 (Connective x arity))))
pattern SeqBox            = FX (Lx2 (Lx1 (Lx4 (Connective Box AOne))))
pattern SeqDia            = FX (Lx2 (Lx1 (Lx4 (Connective Diamond AOne))))
pattern SeqIndexer        = FX (Lx2 (Lx2 (Lx1 AtIndex)))
pattern SeqIndicies c a   = FX (Lx2 (Lx2 (Lx2 (Function c a))))
pattern SeqIdxCons c a    = FX (Lx2 (Lx2 (Lx3 (Function c a))))
pattern LFalsum           = FX (Lx2 (Lx1 (Lx5 (Connective Falsum AZero))))
pattern SeqProp n         = SeqP (Prop n) AZero
pattern SeqPhi :: Int -> WorldTheorySequentCalc (Form (World -> Bool))
pattern SeqPhi n          = SeqSP (SProp n) AZero
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
pattern SeqNeg x          = SeqNot :!$: x
pattern SeqIndex n        = SeqIndicies (Constant n) AZero
pattern SeqCons x y       = SeqIdxCons IndexCons ATwo :!$: x :!$: y

instance Eq (WorldTheorySequentCalc a) where
        (==) = (=*)

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

axiom = [
        ] ∴ SA (SeqPhi 1) :|-: SS (SeqPhi 1)

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

negatedConditionalVariations = [
                [ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :->-: SeqPhi 2)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :&-: SeqNeg (SeqPhi 2))
            ,
                [ GammaV 1 :|-: SS (SeqPhi 1 :&-: SeqNeg (SeqPhi 2))
                ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :->-: SeqPhi 2)
            ]

negatedConjunctionVariations = [
                [ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :&-: SeqPhi 2)
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqNeg (SeqPhi 2))
            ,
                [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqNeg (SeqPhi 2))
                ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :&-: SeqPhi 2)
            ]

negatedBiconditionalVariations = [
                [ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :<->-: SeqPhi 2)
                ] ∴ GammaV 1 :|-: SS (SeqNeg (SeqPhi 1) :<->-: SeqPhi 2)
            ,
                [ GammaV 1 :|-: SS (SeqNeg (SeqPhi 1) :<->-: SeqPhi 2)
                ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :<->-: SeqPhi 2)
            ]

deMorgansNegatedOr = [
                [ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :||-: SeqPhi 2)
                ] ∴ GammaV 1 :|-: SS (SeqNeg (SeqPhi 1) :&-: SeqNeg (SeqPhi 2))
            ,
                [ GammaV 1 :|-: SS (SeqNeg (SeqPhi 1) :&-: SeqNeg (SeqPhi 2))
                ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqPhi 1 :||-: SeqPhi 2)
            ]

-------------------------------
--  1.2.2 Replacement Rules  --
-------------------------------

-- replace :: PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> [SequentRule PurePropLexicon]
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
