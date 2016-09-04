{-#LANGUAGE ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable, FunctionalDependencies #-}
module Carnap.Languages.ClassicalSequent.Syntax where

import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (checkChildren)
import Carnap.Core.Util
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Core.Util
import Carnap.Languages.Util.LanguageClasses
import Control.Lens.Plated (transform, children)
import Control.Lens.Prism
import Data.Typeable
import Carnap.Languages.Util.GenericConnectives


--------------------------------------------------------
--1. Sequent Data
--------------------------------------------------------

data Antecedent = Antecedent

data Succedent = Succedent

data Sequent = Sequent

data Cedent :: k -> * -> * where
        NilAntecedent    :: Cedent lang Antecedent
        NilSuccedent     :: Cedent lang Succedent
        SingleAntecedent :: Cedent lang (Form Bool -> Antecedent)
        SingleSuccedent  :: Cedent lang (Form Bool -> Succedent)

instance Schematizable (Cedent a) where
        schematize NilAntecedent xs = "⊤"
        schematize NilSuccedent xs = "⊥"
        schematize SingleAntecedent (x:xs) = x
        schematize SingleSuccedent (x:xs) = x 

instance FirstOrderLex (Cedent a)

instance Monad m => MaybeMonadVar (Cedent a) m

instance UniformlyEq (Cedent a) where
        NilAntecedent =* NilAntecedent = True
        NilSuccedent =* NilSuccedent = True
        SingleAntecedent =* SingleAntecedent = True
        SingleSuccedent =* SingleSuccedent = True
        _ =* _ = False

data CedentVar :: k -> * -> * where
        Gamma :: Int -> CedentVar lang Antecedent
        Delta :: Int -> CedentVar lang Succedent

instance UniformlyEq (CedentVar a) where
        Gamma n =* Gamma m = n == m
        Delta n =* Delta m = n == m
        _ =* _ = False

instance Schematizable (CedentVar a) where
        schematize (Gamma n) [] = "Γ_" ++ show n
        schematize (Delta n) [] = "Δ_" ++ show n

instance FirstOrderLex (CedentVar a) where
        isVarLex _ = True

instance Monad m => MaybeMonadVar (CedentVar a) m

data Comma :: k -> * -> * where
        AnteComma :: Comma lang (Antecedent -> Antecedent -> Antecedent)
        SuccComma :: Comma lang (Succedent -> Succedent-> Succedent)

instance UniformlyEq (Comma a) where
        AnteComma =* AnteComma = True
        SuccComma =* SuccComma = True
        _ =* _ = False

instance Schematizable (Comma a) where
        schematize AnteComma (x:"⊤":[]) = x
        schematize AnteComma (x:y:[])  = x ++ "," ++ y
        schematize SuccComma (x:"⊥":[]) = x
        schematize SuccComma (x:y:[])  = x ++ "," ++ y

instance FirstOrderLex (Comma a)

instance Monad m => MaybeMonadVar (Comma a) m

data Turnstile :: k -> * -> * where
        Turnstile :: Turnstile lang (Antecedent -> Succedent -> Sequent)

instance Schematizable (Turnstile a) where
        schematize Turnstile (x:y:xs) = x ++ " ⊢ " ++ y

instance FirstOrderLex (Turnstile a)

instance UniformlyEq (Turnstile a) where
        Turnstile =* Turnstile = True
        _ =* _ = False

instance Monad m => MaybeMonadVar (Turnstile a) m

type ClassicalSequentLex = Cedent
                           :|: Comma
                           :|: Turnstile
                           :|: CedentVar
                           :|: SubstitutionalVariable
                           :|: EndLang

type ClassicalSequentOver a = FixLang (ClassicalSequentLex :|: a :|: EndLang)

pattern Top                 = FX (Lx1 (Lx1 NilAntecedent))
pattern Bot                 = FX (Lx1 (Lx1 NilSuccedent))
pattern SA x                = FX (Lx1 (Lx1 SingleAntecedent)) :!$: x
pattern SS x                = FX (Lx1 (Lx1 SingleSuccedent)) :!$: x
pattern (:+:) x y           = FX (Lx1 (Lx2 AnteComma)) :!$: x :!$: y
pattern (:-:) x y           = FX (Lx1 (Lx2 SuccComma)) :!$: x :!$: y
pattern (:|-:) x y          = FX (Lx1 (Lx3 Turnstile)) :!$: x :!$: y
pattern GammaV n            = FX (Lx1 (Lx4 (Gamma n)))
pattern DeltaV n            = FX (Lx1 (Lx4 (Delta n)))
pattern SV n                = FX (Lx1 (Lx5 (SubVar n)))

instance (FirstOrderLex (t (ClassicalSequentOver t))) =>
        ACUI (ClassicalSequentOver t) where

        unfoldTerm (x :+: y) = unfoldTerm x ++ unfoldTerm y
        unfoldTerm Top       = []
        unfoldTerm leaf      = [leaf]

        isId Top = True
        isId _   = False

        -- isACUI Top        = True
        -- isACUI (SA _)     = True
        -- isACUI (GammaV _) = True
        -- --isACUI (SV _)     = True
        -- isACUI (_ :+: _)  = True
        isACUI (SA _)     = False
        isACUI _ = True
        

        getId (Proxy :: Proxy a) = 
            case eqT :: Maybe (a :~: Antecedent) of
               Just Refl -> Top
               _         -> error "you have to use the right type 1"

        acuiOp a Top = a
        acuiOp Top b = b
        acuiOp x@(_ :+: _) y   = x :+: y
        acuiOp x y@(_ :+: _)   = x :+: y
        acuiOp x@(SA _) y = x :+: y
        acuiOp x y@(SA _) = x :+: y
        acuiOp x@(GammaV _) y  = x :+: y
        acuiOp x y@(GammaV _)  = x :+: y
        acuiOp ((SV n) :: ClassicalSequentOver t a) b = 
            case eqT :: Maybe (a :~: Antecedent) of
                Just Refl -> (SV n) :+: b
                _         -> error "you have to use the right type 2"
        acuiOp a ((SV n) :: ClassicalSequentOver t a) = 
            case eqT :: Maybe (a :~: Antecedent) of
                Just Refl -> a :+: (SV n)
                _         -> error "you have to use the right type 3"

--------------------------------------------------------
--2. Sequent Languages
--------------------------------------------------------

class Sequentable f where
        liftToSequent :: FixLang f a -> ClassicalSequentOver f a

--------------------------------------------------------
--2.1 Propositional Sequent Calculus
--------------------------------------------------------

type PropSequentCalc = ClassicalSequentOver PurePropLexicon

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema PropSequentCalc

pattern SeqP x arity      = FX (Lx2 (Lx1 (Predicate x arity)))
pattern SeqSP x arity     = FX (Lx2 (Lx2 (Predicate x arity)))
pattern SeqCon x arity    = FX (Lx2 (Lx3 (Connective x arity)))
pattern SeqProp n         = SeqP (Prop n) AZero
pattern SeqPhi n          = SeqSP (SProp n) AZero
pattern SeqAnd            = SeqCon And ATwo
pattern SeqOr             = SeqCon Or ATwo
pattern SeqIf             = SeqCon If ATwo
pattern SeqIff            = SeqCon Iff ATwo
pattern SeqNot            = SeqCon Not AOne
pattern (:&-:) x y        = SeqAnd :!$: x :!$: y
pattern (:||-:) x y       = SeqOr  :!$: x :!$: y
pattern (:->-:) x y       = SeqIf  :!$: x :!$: y
pattern (:<->-:) x y      = SeqIff :!$: x :!$: y
pattern SeqNeg x          = SeqNot :!$: x

data PropSeqLabel = PropSeqFO | PropSeqACUI
        deriving (Eq, Ord, Show)

instance Eq (PropSequentCalc a) where
        (==) = (=*)

instance Combineable PropSequentCalc PropSeqLabel where

    getLabel Top               = PropSeqACUI
    getLabel (_ :+: _)         = PropSeqACUI
    getLabel (GammaV _)        = PropSeqACUI
    --getLabel (SA     _)        = PropSeqACUI
    getLabel _                 = PropSeqFO

    getAlgo PropSeqFO   = foUnifySys
    getAlgo PropSeqACUI = acuiUnifySys

    replaceChild (_ :&-: x)   pig 0 = unEveryPig pig :&-: x
    replaceChild (x :&-: _)   pig 1 = x :&-: unEveryPig pig
    replaceChild (_ :||-: x)  pig 0 = unEveryPig pig :||-: x
    replaceChild (x :||-: _)  pig 1 = x :||-: unEveryPig pig
    replaceChild (_ :->-: x)  pig 0 = unEveryPig pig :->-: x
    replaceChild (x :->-: _)  pig 1 = x :->-: unEveryPig pig
    replaceChild (_ :<->-: x) pig 0 = unEveryPig pig :<->-: x
    replaceChild (x :<->-: _) pig 1 = x :<->-: unEveryPig pig
    replaceChild (_ :+: x)    pig 0 = unEveryPig pig :+: x
    replaceChild (x :+: _)    pig 1 = x :+: unEveryPig pig
    replaceChild (_ :-: x)    pig 0 = unEveryPig pig :-: x
    replaceChild (x :-: _)    pig 1 = x :-: unEveryPig pig
    replaceChild (_ :|-: x)   pig 0 = unEveryPig pig :|-: x
    replaceChild (x :|-: _)   pig 1 = x :|-: unEveryPig pig
    replaceChild (SeqNeg _)   pig _ = SeqNeg $ unEveryPig pig
    replaceChild (SS _ )      pig _ = SS $ unEveryPig pig 
    replaceChild (SA _ )      pig _ = SA $ unEveryPig pig

instance Sequentable PurePropLexicon where
    liftToSequent (x :&: y)     = (liftToSequent x :&-: liftToSequent y)
    liftToSequent (x :||: y)    = (liftToSequent x :||-: liftToSequent y)
    liftToSequent (x :->: y)    = (liftToSequent x :->-: liftToSequent y)
    liftToSequent (x :<->: y)   = (liftToSequent x :<->-: liftToSequent y)
    liftToSequent (PNeg y)      = (SeqNeg $ liftToSequent y)
    liftToSequent (PP n)        = SeqProp n
