module Carnap.Languages.Util.LanguageClasses where

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

class ModalLanguage l where
        nec :: l -> l
        pos :: l -> l
