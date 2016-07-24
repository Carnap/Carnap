{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.ClassicalSequent.Syntax (
) where

import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (checkChildren)
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Core.Util
import Carnap.Languages.Util.LanguageClasses
import Control.Lens.Plated (transform, children)
import Control.Lens.Prism
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConnectives


--------------------------------------------------------
--1. Sequent Data
--------------------------------------------------------

data Antecedent = Antecedent

data Succedent = Succedent

data Sequent = Sequent

data Nilcedent :: k -> * -> * where
        NilAntecedent :: Nilcedent lang Antecedent
        NilSuccedent  :: Nilcedent lang Succedent

instance Schematizable (Nilcedent a) where
        schematize NilAntecedent xs = ""
        schematize NilSuccedent xs = ""

data Comma :: k -> * -> * where
        AnteComma :: Comma lang (Form Bool -> Antecedent -> Antecedent)
        SuccComma :: Comma lang (Form Bool -> Succedent-> Succedent)

instance Schematizable (Comma a) where
        schematize AnteComma (x:"":[]) = x
        schematize AnteComma (x:y:[])  = x ++ "," ++ y
        schematize SuccComma (x:"":[]) = x
        schematize SuccComma (x:y:[])  = x ++ "," ++ y

data Turnstile :: k -> * -> * where
        Turnstile :: Turnstile lang (Antecedent -> Succedent -> Sequent)

instance Schematizable (Turnstile a) where
        schematize Turnstile (x:y:xs) = x ++ " ⊢ " ++ y

type ClassicalSequentLex = Nilcedent
                           :|: Comma
                           :|: Turnstile 
                           :|: EndLang

type ClassicalSequentOver a = FixLang (ClassicalSequentLex :|: a)


pattern Top                 = FX (Lx1 (Lx1 NilAntecedent))
pattern Bot                 = FX (Lx1 (Lx1 NilSuccedent))
pattern (:+:) x y           = FX (Lx1 (Lx2 AnteComma)) :!$: x :!$: y
pattern (:-:) x y           = FX (Lx1 (Lx2 SuccComma)) :!$: x :!$: y
-- --We're unlikely to be doing anything with multi-conclusion sequents right now
pattern (:|-:) :: ClassicalSequentOver a Antecedent -> ClassicalSequentOver a (Form Bool) -> ClassicalSequentOver a Sequent
pattern (:|-:) x y          = FX (Lx1 (Lx3 Turnstile)) :!$: x :!$: (y :-: Bot)

--------------------------------------------------------
--2. Sequent Languages
--------------------------------------------------------

type PropSequentCalc = ClassicalSequentOver (PurePropLexicon :|: EndLang)

instance CopulaSchema PropSequentCalc

pattern SeqP x arity      = FX (Lx2 (Lx1 (Predicate x arity)))
pattern SeqSP x arity     = FX (Lx2 (Lx2 (Predicate x arity)))
pattern SeqCon x arity    = FX (Lx2 (Lx3 (Connective x arity)))
pattern SeqProp n         = SeqP (Prop n) AZero
