{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.Util.GenericConnectives where

import Carnap.Core.Data.AbstractSyntaxDataTypes

data IntProp b a where
        Prop :: Int -> IntProp b (Form b)

instance Schematizable (IntProp b) where
        schematize (Prop n)   _       = "P_" ++ show n

data BooleanConn b a where
        And :: BooleanConn b (Form b -> Form b -> Form b)
        Or :: BooleanConn b (Form b -> Form b -> Form b)
        If :: BooleanConn b (Form b -> Form b -> Form b)
        Iff :: BooleanConn b (Form b -> Form b -> Form b)
        Not :: BooleanConn b (Form b -> Form b)

instance Schematizable (BooleanConn b) where
        schematize Iff = \(x:y:_) -> "(" ++ x ++ " ↔ " ++ y ++ ")"
        schematize If  = \(x:y:_) -> "(" ++ x ++ " → " ++ y ++ ")"
        schematize Or = \(x:y:_) -> "(" ++ x ++ " ∨ " ++ y ++ ")"
        schematize And = \(x:y:_) -> "(" ++ x ++ " ∧ " ++ y ++ ")"
        schematize Not = \(x:_) -> "¬" ++ x

data SchematicIntProp b a where
        SProp :: Int -> SchematicIntProp b (Form b)

instance Schematizable (SchematicIntProp b) where
        schematize (SProp n)   _       = "φ_" ++ show n
--XXX:All Schematic Propositions are false. A better solution might make
--a schematic language take semantic values in a Maybe monad
