{-#LANGUAGE MultiParamTypeClasses #-}
module Carnap.Languages.Util.LanguageClasses where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Data.Typeable

--------------------------------------------------------
--1. Connectives
--------------------------------------------------------
--------------------------------------------------------
--1.1 Boolean Languages
--------------------------------------------------------
--these are classes and datatypes for languages and schematic languages
--with boolean connectives

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

class IndexedPropLanguage l where
        pn :: Int -> l

class IndexedSchemePropLanguage l where
        phin :: Int -> l

class PolyadicPredicateLanguage l arg ret where
        ppn :: Int -> Arity arg ret n ret' -> FixLang l ret'
        --This needs to provide a way of bumping up the arity of a given
        --predicate

class IncrementablePredicate l arg where
        incHead :: FixLang l a -> Maybe (FixLang l (arg -> a)) 
        incPred :: (Typeable b, Typeable arg) => FixLang l (arg -> b) -> Maybe (FixLang l (arg -> arg -> b))
        incPred = incArity incHead


class ModalLanguage l where
        nec :: l -> l
        pos :: l -> l

class QuantLanguage l t where
        lall  :: String -> (t -> l) -> l
        lsome :: String -> (t -> l) -> l

class EqLanguage l t where
        equals :: t -> t -> l
