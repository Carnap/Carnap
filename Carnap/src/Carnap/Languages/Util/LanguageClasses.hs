{-#LANGUAGE MultiParamTypeClasses, TypeOperators #-}
module Carnap.Languages.Util.LanguageClasses where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (incArity)
import Data.Typeable


--The convention for variables in this module is that lex is
--a lexicon, lang is language (without a particular associated syntactic
--type) and l is a language with an associated syntactic type

--------------------------------------------------------
--1. Connectives
--------------------------------------------------------
--------------------------------------------------------
--1.1 Boolean Languages
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

--------------------------------------------------------
--1.2 Modal Languages
--------------------------------------------------------

class ModalLanguage l where
        nec :: l -> l
        pos :: l -> l

class IndexedPropLanguage l where
        pn :: Int -> l

class IndexedSchemePropLanguage l where
        phin :: Int -> l

class IndexedConstantLanguage l where
        cn :: Int -> l

class PolyadicPredicateLanguage lang arg ret where
        ppn :: Typeable ret' => Int -> Arity arg ret n ret' -> lang ret'

class PolyadicFunctionLanguage lang arg ret where
        pfn :: Typeable ret' => Int -> Arity arg ret n ret' -> lang ret'

class Incrementable lex arg where
        incHead :: FixLang lex a -> Maybe (FixLang lex (arg -> a)) 
        incBody :: (Typeable b, Typeable arg) => FixLang lex (arg -> b) -> Maybe (FixLang lex (arg -> arg -> b))
        incBody = incArity incHead


class QuantLanguage l t where
        lall  :: String -> (t -> l) -> l
        lsome :: String -> (t -> l) -> l

class EqLanguage l t where
        equals :: t -> t -> l

class f :<: g where
        liftLang :: FixLang f a -> FixLang g a
        sinkLang :: FixLang g a -> FixLang f a
        --- TODO : add assocatied prism, viewed as partial iso
