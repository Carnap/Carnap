{-#LANGUAGE MultiParamTypeClasses, TypeOperators #-}
module Carnap.Languages.Util.LanguageClasses where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (incArity)
import Data.Typeable


--The convention for variables in this module is that lex is
--a lexicon, lang is language (without a particular associated syntactic
--type) and l is a language with an associated syntactic type

--------------------------------------------------------
--1. Constructor classes
--------------------------------------------------------

--------------------------------------------------------
--1.1 Connectives
--------------------------------------------------------
--------------------------------------------------------
--1.1.1 Boolean Languages
--------------------------------------------------------
--these are classes and datatypes for languages and schematic languages
--with boolean connectives. 
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

class IndexedPropContextSchemeLanguage l where
            propCtx :: Int -> l -> l

--------------------------------------------------------
--1.1.2 Modal Languages
--------------------------------------------------------

class ModalLanguage l where
        nec :: l -> l
        pos :: l -> l

--------------------------------------------------------
--1.2 Propositions
--------------------------------------------------------

--------------------------------------------------------
--1.2.1 Propositional Languages
--------------------------------------------------------
--languages with propositions

class IndexedPropLanguage l where
        pn :: Int -> l

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
