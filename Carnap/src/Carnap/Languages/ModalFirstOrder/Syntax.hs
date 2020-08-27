{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Languages.ModalFirstOrder.Syntax
where

import Carnap.Core.Util 
import Carnap.Languages.ModalPropositional.Syntax (World, ModalPropLexiconWith, AbsoluteModalLexicon)
import Carnap.Languages.PureFirstOrder.Syntax (foVar)
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Util (scopeHeight, castTo)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Control.Lens (Traversal', preview, outside, (.~), (&), Prism')
import Data.Typeable (Typeable)
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

instance FirstOrder (FixLang (ModalFirstOrderLexOverWith b a)) => 
    BoundVars (ModalFirstOrderLexOverWith b a) where

    scopeUniqueVar q (LLam f) = case castTo $ foVar $ show $ scopeHeight (LLam f) of
                                    Just x -> x
                                    Nothing -> error "cast failed in ScopeUniqueVar"
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance PrismPropLex (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismIndexedConstant (ModalFirstOrderLexOverWith b a) Int
instance PrismBooleanConnLex (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismGenericContext (ModalFirstOrderLexOverWith b a) (World -> Bool) (World -> Bool)
instance PrismBooleanConst (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismSchematicProp (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismGenericQuant (ModalFirstOrderLexOverWith b a) Term Form (World -> Bool) Int
instance PrismModality (ModalFirstOrderLexOverWith b a) (World -> Bool)
instance PrismPolyadicPredicate (ModalFirstOrderLexOverWith b a) Int (World -> Bool)
instance PrismPolyadicSchematicPredicate (ModalFirstOrderLexOverWith b a) Int (World -> Bool)
instance PrismPolyadicSchematicFunction (ModalFirstOrderLexOverWith b a) Int Int
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

    appSchema q@(Fx _) (LLam f) e = case ( qtype q >>= preview _all >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         ) of
                                     (Just (x,v), _) -> schematize (All x) (show (f v) : e)
                                     (_, Just (x,v)) -> schematize (Some x) (show (f v) : e)
                                     _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

-------------------------------------
--  2.1.1 Simplest Modal Extension --
-------------------------------------

type SimpleModalFirstOrderLanguage = SimpleModalFirstOrderLanguageWith EndLang

type SimpleModalFirstOrderLex = SimpleModalFirstOrderLexWith EndLang

instance Incrementable SimpleModalFirstOrderLex (Term Int) where
    incHead = const Nothing
        & outside (_predIdx')  .~ (\(n,a) -> Just $ ppn n (ASucc a))
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_sfuncIdx') .~ (\(n,a) -> Just $ spfn n (ASucc a))
        where _predIdx' :: Typeable ret => Prism' (SimpleModalFirstOrderLanguage ret) (Int, Arity (Term Int) (Form (World -> Bool)) ret) 
              _predIdx' = _predIdx
              _spredIdx' :: Typeable ret => Prism' (SimpleModalFirstOrderLanguage ret) (Int, Arity (Term Int) (Form (World -> Bool)) ret) 
              _spredIdx' = _spredIdx
              _sfuncIdx' :: Typeable ret => Prism' (SimpleModalFirstOrderLanguage ret) (Int, Arity (Term Int) (Term Int) ret) 
              _sfuncIdx' = _sfuncIdx

----------------------------------
--  2.2 Indexed Modal Extension --
----------------------------------

type IndexedModalFirstOrderLanguageWith a = ModalFirstOrderLanguageOverWith AbsoluteModalLexicon a

type IndexedModalFirstOrderLexWith a = ModalFirstOrderLexOverWith AbsoluteModalLexicon a

instance ( Schematizable (a (IndexedModalFirstOrderLanguageWith a))
         , StaticVar (IndexedModalFirstOrderLanguageWith  a)
         ) => CopulaSchema (IndexedModalFirstOrderLanguageWith a) where 

    appSchema q@(Fx _) (LLam f) e = case ( qtype q >>= preview _all >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         ) of
                                     (Just (x,v), _) -> schematize (All x) (show (f v) : e)
                                     (_, Just (x,v)) -> schematize (Some x) (show (f v) : e)
                                     _ -> schematize q (show (LLam f) : e)
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
    incHead = const Nothing
        & outside (_predIdx')  .~ (\(n,a) -> Just $ ppn n (ASucc a))
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_sfuncIdx') .~ (\(n,a) -> Just $ spfn n (ASucc a))
        where _predIdx' :: Typeable ret => Prism' (IndexedModalFirstOrderLanguage ret) (Int, Arity (Term Int) (Form (World -> Bool)) ret) 
              _predIdx' = _predIdx
              _spredIdx' :: Typeable ret => Prism' (IndexedModalFirstOrderLanguage ret) (Int, Arity (Term Int) (Form (World -> Bool)) ret) 
              _spredIdx' = _spredIdx
              _sfuncIdx' :: Typeable ret => Prism' (IndexedModalFirstOrderLanguage ret) (Int, Arity (Term Int) (Term Int) ret) 
              _sfuncIdx' = _sfuncIdx

-------------------------
--  Utility Functions  --
-------------------------

qtype :: Typeable a => FixLang lex a -> Maybe (FixLang lex ((Term Int -> Form (World -> Bool))->Form (World -> Bool)))
qtype = castTo
