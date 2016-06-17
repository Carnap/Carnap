{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.Util.GenericConnectives where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses 
import Data.List (intercalate)

data IntProp b a where
        Prop :: Int -> IntProp b (Form b)

instance Schematizable (IntProp b) where
        schematize (Prop n)   _       = "P_" ++ show n

instance FirstOrderLex (IntProp b) where
        sameHeadLex (Prop n) (Prop m) = n == m

data IntPred b c a where
        Pred ::  Arity (Term c) (Form b) n ret -> Int -> IntPred b c ret

instance Schematizable (IntPred b c) where
        schematize (Pred a n) xs = 
            case read $ show a of
                0 -> "P^0_" ++ show n
                m -> "P^" ++ show a ++ "_" ++ show n 
                                        ++ "(" ++ intercalate "," args ++ ")"
                        where args = take m $ xs ++ repeat "_"

instance FirstOrderLex (IntPred b c) where
        sameHeadLex (Pred a n) (Pred a' m) = show a == show a' && n == m

data SchematicIntProp b a where
        SProp :: Int -> SchematicIntProp b (Form b)

instance Schematizable (SchematicIntProp b) where
        schematize (SProp n)   _       = "φ_" ++ show n

instance FirstOrderLex (SchematicIntProp b) where
        isVarLex _ = True
        sameHeadLex (SProp n) (SProp m) = n == m

data IntFunc c b a where
        Func ::  Arity (Term c) (Term b) n ret -> Int -> IntFunc b c ret

instance Schematizable (IntFunc b c) where
        schematize (Func a n) xs = 
            case read $ show a of
                0 -> "f^0_" ++ show n
                m -> "f^" ++ show a ++ "_" ++ show n 
                                        ++ "(" ++ intercalate "," args ++ ")"
                        where args = take m $ xs ++ repeat "_"

instance FirstOrderLex (IntFunc b c) where
        sameHeadLex (Func a n) (Func a' m) = show a == show a' && n == m

instance Evaluable (SchematicIntProp b) where
        eval = error "You should not be able to evaluate schemata"

instance Modelable m (SchematicIntProp b) where
        satisfies = const eval

data SchematicIntPred b c a where
        SPred :: Arity (Term c) (Form b) n ret -> Int -> SchematicIntPred b c ret

instance Schematizable (SchematicIntPred b c) where
        schematize (SPred a n) _ = "φ^" ++ show a ++ "_" ++ show n

instance FirstOrderLex (SchematicIntPred b c) where
        isVarLex _ = True
        sameHeadLex (SPred a n) (SPred a' m) = show a == show a' && n == m

instance Evaluable (SchematicIntPred b c) where
        eval = error "You should not be able to evaluate schemata"

instance Modelable m (SchematicIntPred b c) where
        satisfies = const eval

data TermEq c b a where
        TermEq :: TermEq c b (Term b -> Term b -> Form c)

instance Schematizable (TermEq c b) where
        schematize TermEq = \(t1:t2:_) -> t1 ++ "=" ++ t2

instance FirstOrderLex (TermEq c b) where
        sameHeadLex _ _ = True

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

instance FirstOrderLex (BooleanConn b) where
        sameHeadLex And And = True 
        sameHeadLex Or Or = True 
        sameHeadLex If If = True
        sameHeadLex Iff Iff = True
        sameHeadLex Not Not = True
        sameHeadLex _ _ = False

data Modality b a where
        Box     :: Modality b (Form b -> Form b)
        Diamond :: Modality b (Form b -> Form b)

instance Schematizable (Modality b) where
        schematize Box = \(x:_) -> "□" ++ x
        schematize Diamond = \(x:_) -> "◇" ++ x

instance FirstOrderLex (Modality b) where
        sameHeadLex Box Box = True 
        sameHeadLex Diamond Diamond = True 

data IntConst b a where
        Constant :: Int -> IntConst b (Term b)

instance Schematizable (IntConst b) where
        schematize (Constant n)   _       = "c_" ++ show n

instance FirstOrderLex (IntConst b) where
        sameHeadLex (Constant n) (Constant m) = n == m

data StandardQuant b c a where
        All  :: String -> StandardQuant b c ((Term c -> Form b) -> Form b)
        Some :: String -> StandardQuant b c ((Term c -> Form b) -> Form b)

instance Schematizable (StandardQuant b c) where
        schematize (All v) = \(x:_) -> "∀" ++ v ++ "(" ++ x ++ ")"
        schematize (Some v) = \(x:_) -> "∃" ++ v ++ "(" ++ x ++ ")"

instance FirstOrderLex (StandardQuant b c) where
        sameHeadLex (All _) (All _) = True
        sameHeadLex (Some _) (Some _) = True

data StandardVar b a where
    Var :: String -> StandardVar b (Term b)

instance Schematizable (StandardVar b) where
        schematize (Var s) = const s

instance FirstOrderLex (StandardVar b) where
        sameHeadLex (Var n) (Var m) = n == m
