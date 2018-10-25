{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Languages.ModalFirstOrder.Syntax
where

import Carnap.Core.Util 
import Carnap.Languages.ModalPropositional.Syntax (World, ModalPropLexiconWith, AbsoluteModalLexicon)
import Carnap.Languages.PureFirstOrder.Syntax (foVar)
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConstructors
import Data.List (intercalate)

--------------------------------------------------------
--1. Data for Modal First Order Logic
--------------------------------------------------------

type ModalPredicate = IntPred (World -> Bool) Int

type ModalFunction = IntFunc Int Int

type ModalSchematicFunc = SchematicIntFunc Int Int

type ModalEq = TermEq (World -> Bool) Int

type ModalSchematicPred = SchematicIntPred (World -> Bool) Int

type ModalConstant = IntConst Int

type ModalVar = StandardVar Int

type ModalQuant = StandardQuant (World -> Bool) Int

--------------------------------------------------------
--2. Modal Polyadic First Order Languages 
--------------------------------------------------------

--------------------------------------------------------
--2.0 Common Core
--------------------------------------------------------

type CoreLexiconOver b = ModalPropLexiconWith b
                       :|: Binders ModalQuant
                       :|: Predicate ModalPredicate     
                       :|: Function ModalConstant
                       :|: Function ModalVar
                       :|: Function ModalSchematicFunc
                       :|: Predicate ModalSchematicPred     
                       :|: EndLang

type ModalFirstOrderLexOverWith b a = CoreLexiconOver b :|: a

type ModalFirstOrderLanguageOverWith b a = FixLang (ModalFirstOrderLexOverWith b a)

pattern PQuant q       = FX (Lx1 (Lx2 (Bind q)))
pattern PPred x arity  = FX (Lx1 (Lx3 (Predicate x arity)))
pattern PBind q f      = PQuant q :!$: LLam f
pattern PP n a1 a2     = PPred (Pred a1 n) a2

instance FirstOrder (FixLang (ModalFirstOrderLexOverWith b a)) => 
    BoundVars (ModalFirstOrderLexOverWith b a) where

    scopeUniqueVar (PQuant (Some v)) (LLam f) = foVar $ show $ scopeHeight (LLam f)
    scopeUniqueVar (PQuant (All v)) (LLam f)  = foVar $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance PrismPropLex (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismIndexedConstant (ModalFirstOrderLexOverWith b a) Int
instance PrismBooleanConnLex (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismPropositionalContext (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismBooleanConst (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismSchematicProp (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismStandardQuant (ModalFirstOrderLexOverWith b a) (World -> Bool) Int
instance PrismModality (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismPolyadicPredicate (ModalFirstOrderLexOverWith b a) Int (World -> Bool)
instance PrismPolyadicSchematicPredicate (ModalFirstOrderLexOverWith b a) Int (World -> Bool)
instance PrismStandardVar (ModalFirstOrderLexOverWith b a) Int
instance PrismSubstitutionalVariable (ModalFirstOrderLexOverWith b a)

--equality up to α-equivalence
instance UniformlyEq (ModalFirstOrderLanguageOverWith b a) => Eq (ModalFirstOrderLanguageOverWith b a c) where
        (==) = (=*)

---------------------------------
--  2.1 Simple Modal Extension --
---------------------------------

type SimpleModalFirstOrderLanguageWith a = ModalFirstOrderLanguageOverWith EndLang a

type SimpleModalFirstOrderLexWith a = ModalFirstOrderLexOverWith EndLang a

instance ( Schematizable (a (SimpleModalFirstOrderLanguageWith a))
         , StaticVar (SimpleModalFirstOrderLanguageWith  a)
         ) => CopulaSchema (SimpleModalFirstOrderLanguageWith a) where 

    appSchema (PQuant (All x)) (LLam f) e = schematize (All x) (show (f $ foVar x) : e)
    appSchema (PQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ foVar x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

-------------------------------------
--  2.1.1 Simplest Modal Extension --
-------------------------------------

type SimpleModalFirstOrderLanguage = SimpleModalFirstOrderLanguageWith EndLang

type SimpleModalFirstOrderLex = SimpleModalFirstOrderLexWith EndLang

instance Incrementable SimpleModalFirstOrderLex (Term Int) where
    incHead (PP n a b) = Just $ PP n (ASucc a) (ASucc a)
    incHead _  = Nothing

----------------------------------
--  2.2 Indexed Modal Extension --
----------------------------------

type IndexedModalFirstOrderLanguageWith a = ModalFirstOrderLanguageOverWith AbsoluteModalLexicon a

type IndexedModalFirstOrderLexWith a = ModalFirstOrderLexOverWith AbsoluteModalLexicon a

instance ( Schematizable (a (IndexedModalFirstOrderLanguageWith a))
         , StaticVar (IndexedModalFirstOrderLanguageWith  a)
         ) => CopulaSchema (IndexedModalFirstOrderLanguageWith a) where 

    appSchema (PQuant (All x)) (LLam f) e = schematize (All x) (show (f $ foVar x) : e)
    appSchema (PQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ foVar x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f $ static (-1 * h))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f $ static (-1 * h)) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

instance PrismIndexing (IndexedModalFirstOrderLexWith a) World (World -> Bool) Bool
instance PrismIntIndex (IndexedModalFirstOrderLexWith a) World
instance PrismCons (IndexedModalFirstOrderLexWith a) World
instance PrismPolyadicSchematicFunction (IndexedModalFirstOrderLexWith a) World World

---------------------------------------------
--  2.2.1 Simplest Indexed Modal Extension --
---------------------------------------------

type IndexedModalFirstOrderLanguage = IndexedModalFirstOrderLanguageWith EndLang

type IndexedModalFirstOrderLex = IndexedModalFirstOrderLexWith EndLang 

instance Incrementable IndexedModalFirstOrderLex (Term Int) where
    incHead (PP n a b) = Just $ PP n (ASucc a) (ASucc a)
    incHead _  = Nothing
