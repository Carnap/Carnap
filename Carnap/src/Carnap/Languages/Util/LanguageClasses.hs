{-#LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, TypeOperators, GADTs, ScopedTypeVariables #-}
module Carnap.Languages.Util.LanguageClasses where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (incArity)
import Carnap.Languages.Util.GenericConstructors
import Data.Typeable
import Control.Lens


--The convention for variables in this module is that lex is
--a lexicon, lang is language (without a particular associated syntactic
--type) and l is a language with an associated syntactic type

--------------------------------------------------------
--1. Constructor classes
--------------------------------------------------------

--------------------------------------------------------
--1.1 Connectives
--------------------------------------------------------

--these are classes for languages and with boolean connectives. 
class BooleanLanguage l where
            lneg :: l -> l
            land :: l -> l -> l
            lor  :: l -> l -> l
            lif  :: l -> l -> l
            liff :: l -> l -> l
            (.¬.) :: l -> l 
            (.¬.) = lneg
            (.-.) :: l -> l 
            (.-.) = lneg
            (.→.) :: l -> l -> l
            (.→.) = lif
            (.=>.) :: l -> l -> l
            (.=>.) = lif
            (.∧.) :: l -> l -> l
            (.∧.) = land
            (./\.) :: l -> l -> l
            (./\.) = land
            (.∨.) :: l -> l -> l
            (.∨.) = lor
            (.\/.) :: l -> l -> l
            (.\/.) = lor
            (.↔.) :: l -> l -> l
            (.↔.) = liff
            (.<=>.) :: l -> l -> l
            (.<=>.) = liff

class (Typeable b, PrismLink (FixLang lex) (Connective (BooleanConn b) (FixLang lex))) 
        => PrismBooleanConnLex lex b where

        _and :: Prism' (FixLang lex (Form b -> Form b -> Form b)) ()
        _and = binarylink_PrismBooleanConnLex . andPris 

        _or :: Prism' (FixLang lex (Form b -> Form b -> Form b)) ()
        _or = binarylink_PrismBooleanConnLex . orPris 

        _if :: Prism' (FixLang lex (Form b -> Form b -> Form b)) ()
        _if = binarylink_PrismBooleanConnLex . ifPris 

        _iff :: Prism' (FixLang lex (Form b -> Form b -> Form b)) ()
        _iff = binarylink_PrismBooleanConnLex . iffPris 

        _not :: Prism' (FixLang lex (Form b -> Form b)) ()
        _not = unarylink_PrismBooleanConnLex . notPris 

        binarylink_PrismBooleanConnLex :: 
            Prism' (FixLang lex (Form b -> Form b -> Form b)) 
                   (Connective (BooleanConn b) (FixLang lex) (Form b -> Form b -> Form b))
        binarylink_PrismBooleanConnLex = link 

        unarylink_PrismBooleanConnLex :: 
            Prism' (FixLang lex (Form b -> Form b)) 
                   (Connective (BooleanConn b) (FixLang lex) (Form b -> Form b))
        unarylink_PrismBooleanConnLex = link 

        andPris :: Prism' (Connective (BooleanConn b) (FixLang lex) (Form b -> Form b -> Form b)) ()
        andPris = prism' (\_ -> Connective And ATwo) 
                          (\x -> case x of Connective And ATwo -> Just (); _ -> Nothing)

        orPris :: Prism' (Connective (BooleanConn b) (FixLang lex) (Form b -> Form b -> Form b)) ()
        orPris = prism' (\_ -> Connective Or ATwo) 
                         (\x -> case x of Connective Or ATwo -> Just (); _ -> Nothing)

        ifPris :: Prism' (Connective (BooleanConn b) (FixLang lex) (Form b -> Form b -> Form b)) ()
        ifPris = prism' (\_ -> Connective If ATwo) 
                         (\x -> case x of Connective If ATwo -> Just (); _ -> Nothing)

        iffPris :: Prism' (Connective (BooleanConn b) (FixLang lex) (Form b -> Form b -> Form b)) ()
        iffPris = prism' (\_ -> Connective Iff ATwo) 
                          (\x -> case x of Connective Iff ATwo -> Just (); _ -> Nothing)

        notPris :: Prism' (Connective (BooleanConn b) (FixLang lex) (Form b -> Form b)) ()
        notPris = prism' (\_ -> Connective Not AOne) 
                          (\x -> case x of Connective Not AOne -> Just (); _ -> Nothing)

class IndexedPropContextSchemeLanguage l where
            propCtx :: Int -> l -> l

class ModalLanguage l where
        nec :: l -> l
        pos :: l -> l

class BooleanConstLanguage l where 
        lverum :: l
        lfalsum :: l

--------------------------------------------------------
--1.2 Propositions
--------------------------------------------------------

--------------------------------------------------------
--1.2.1 Propositional Languages
--------------------------------------------------------
--languages with propositions
--TODO: derive IndexedPropLanguage from PrismPropLex

class IndexedPropLanguage l where
        pn :: Int -> l

class (Typeable b, PrismLink (FixLang lex) (Predicate (IntProp b) (FixLang lex))) 
        => PrismPropLex lex b where

        propIndex :: Prism' (FixLang lex (Form b)) Int
        propIndex = link_PrismPropLex . propIndex'

        link_PrismPropLex :: Prism' (FixLang lex (Form b)) (Predicate (IntProp b) (FixLang lex) (Form b))
        link_PrismPropLex = link 

        propIndex' :: Prism' (Predicate (IntProp b) (FixLang lex) (Form b)) Int
        propIndex' = prism' (\n -> Predicate (Prop n) AZero) 
                            (\x -> case x of Predicate (Prop n) AZero -> Just n
                                             _ -> Nothing)

class IndexedSchemePropLanguage l where
        phin :: Int -> l

--------------------------------------------------------
--1.2.2 Predicate Languages
--------------------------------------------------------
--languages with predicates

class PolyadicPredicateLanguage lang arg ret where
        ppn :: Typeable ret' => Int -> Arity arg ret n ret' -> lang ret'

class EqLanguage l t where
        equals :: t -> t -> l

--------------------------------------------------------
--1.3. Terms
--------------------------------------------------------

class IndexedConstantLanguage l where
        cn :: Int -> l

class IndexedSchemeConstantLanguage l where
        taun :: Int -> l

class PolyadicFunctionLanguage lang arg ret where
        pfn :: Typeable ret' => Int -> Arity arg ret n ret' -> lang ret'

--------------------------------------------------------
--1.4. Quantifiers
--------------------------------------------------------

class QuantLanguage l t where
        lall  :: String -> (t -> l) -> l
        lsome :: String -> (t -> l) -> l

--------------------------------------------------------
--2. Utility Classes
--------------------------------------------------------

class Incrementable lex arg where
        incHead :: FixLang lex a -> Maybe (FixLang lex (arg -> a)) 
        incBody :: (Typeable b, Typeable arg) => FixLang lex (arg -> b) -> Maybe (FixLang lex (arg -> arg -> b))
        incBody = incArity incHead
