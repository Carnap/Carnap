{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.Util.GenericConnectives where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses 
import Data.List (intercalate)

data IntProp b a where
        Prop :: Int -> IntProp b (Form b)

instance Schematizable (IntProp b) where
        schematize (Prop n)   _ 
            | n < 0 && n > -12 = ["_PQRSTUVWXYZ" !! (-1 * n)]
            | otherwise = "P_" ++ show n

instance UniformlyEq (IntProp b) where
        (Prop n) =* (Prop m) = n == m

instance Monad m => MaybeMonadVar (IntProp b) m

instance MaybeStaticVar (IntProp b)

instance FirstOrderLex (IntProp b) 

data SchematicIntProp b a where
        SProp :: Int -> SchematicIntProp b (Form b)

instance Schematizable (SchematicIntProp b) where
        schematize (SProp n)   _ 
            | n < 0 && n > -8 = ["_φψχθγζξ" !! (-1 * n)]
            | otherwise = "P_" ++ show n

instance UniformlyEq (SchematicIntProp b) where
        (SProp n) =* (SProp m) = n == m

instance Monad m => MaybeMonadVar (SchematicIntProp b) m

instance MaybeStaticVar (SchematicIntProp b)

instance FirstOrderLex (SchematicIntProp b) where
        isVarLex _ = True

instance Evaluable (SchematicIntProp b) where
        eval = error "You should not be able to evaluate schemata"

instance Modelable m (SchematicIntProp b) where
        satisfies = const eval

data IntPred b c a where
        Pred ::  Arity (Term c) (Form b) n ret -> Int -> IntPred b c ret

instance Schematizable (IntPred b c) where
        schematize (Pred a n) xs = pred ++ tail 
            where arity = read $ show a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | n < 0 && n > -11 = ["_FGHIJKLMO" !! (-1 * n)]
                    | arity == 0       = "P^0_" ++ show n
                    | otherwise        = "P^" ++ show a ++ "_" ++ show n 
                  tail
                    | arity == 0    = ""
                    | otherwise     = "(" ++ intercalate "," args ++ ")"

instance UniformlyEq (IntPred b c) where
        (Pred a n) =* (Pred a' m) = show a == show a' && n == m

instance Monad m => MaybeMonadVar (IntPred b c) m

instance MaybeStaticVar (IntPred b c)

instance FirstOrderLex (IntPred b c)

data SchematicIntPred b c a where
        SPred :: Arity (Term c) (Form b) n ret -> Int -> SchematicIntPred b c ret

instance Schematizable (SchematicIntPred b c) where
        schematize (SPred a n) xs = 
            case read $ show a of
                0 -> "φ^0_" ++ show n
                m -> "φ^" ++ show a ++ "_" ++ show n 
                                        ++ "(" ++ intercalate "," args ++ ")"
                        where args = take m $ xs ++ repeat "_"

instance UniformlyEq (SchematicIntPred b c) where
        (SPred a n) =* (SPred a' m) = show a == show a' && n == m

instance Monad m => MaybeMonadVar (SchematicIntPred b c) m

instance MaybeStaticVar (SchematicIntPred b c)

instance FirstOrderLex (SchematicIntPred b c) where
        isVarLex _ = True

instance Evaluable (SchematicIntPred b c) where
        eval = error "You should not be able to evaluate schemata"

instance Modelable m (SchematicIntPred b c) where
        satisfies = const eval

data IntFunc c b a where
        Func ::  Arity (Term c) (Term b) n ret -> Int -> IntFunc b c ret

instance Schematizable (IntFunc b c) where
        schematize (Func a n) xs = pred ++ tail 
            where arity = read $ show a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | n < 0 && n > -4  = ["_fgh" !! (-1 * n)]
                    | arity == 0       = "f^0_" ++ show n
                    | otherwise        = "f^" ++ show a ++ "_" ++ show n 
                  tail
                    | arity == 0    = ""
                    | otherwise     = "(" ++ intercalate "," args ++ ")"
instance UniformlyEq (IntFunc b c) where
        (Func a n) =* (Func a' m) = show a == show a' && n == m

instance Monad m => MaybeMonadVar (IntFunc b c) m

instance MaybeStaticVar (IntFunc b c)

instance FirstOrderLex (IntFunc b c)

data SchematicIntFunc c b a where
        SFunc ::  Arity (Term c) (Term b) n ret -> Int -> SchematicIntFunc b c ret

instance Schematizable (SchematicIntFunc b c) where
        schematize (SFunc a n) xs = 
            case read $ show a of
                0 -> "τ^0_" ++ show n
                m -> "τ^" ++ show a ++ "_" ++ show n 
                                        ++ "(" ++ intercalate "," args ++ ")"
                        where args = take m $ xs ++ repeat "_"

instance UniformlyEq (SchematicIntFunc b c) where
        (SFunc a n) =* (SFunc a' m) = show a == show a' && n == m

instance Monad m => MaybeMonadVar (SchematicIntFunc b c) m

instance MaybeStaticVar (SchematicIntFunc b c)

instance FirstOrderLex (SchematicIntFunc b c) where
        isVarLex _ = True

data TermEq c b a where
        TermEq :: TermEq c b (Term b -> Term b -> Form c)

instance Schematizable (TermEq c b) where
        schematize TermEq = \(t1:t2:_) -> t1 ++ "=" ++ t2

instance UniformlyEq (TermEq c b) where
        _ =* _ = True

instance Monad m => MaybeMonadVar (TermEq c b) m

instance MaybeStaticVar (TermEq c b)

instance FirstOrderLex (TermEq c b)

data BooleanConn b a where
        And :: BooleanConn b (Form b -> Form b -> Form b)
        Or :: BooleanConn b (Form b -> Form b -> Form b)
        If :: BooleanConn b (Form b -> Form b -> Form b)
        Iff :: BooleanConn b (Form b -> Form b -> Form b)
        Not :: BooleanConn b (Form b -> Form b)

instance Schematizable (BooleanConn b) where
        schematize Iff (x:y:_)  = "(" ++ x ++ " ↔ " ++ y ++ ")"
        schematize Iff []       = "↔"
        schematize If  (x:y:_)  = "(" ++ x ++ " → " ++ y ++ ")"
        schematize If  []       = "→"
        schematize Or  (x:y:_)  = "(" ++ x ++ " ∨ " ++ y ++ ")"
        schematize Or  []       = "∨"
        schematize And (x:y:_)  = "(" ++ x ++ " ∧ " ++ y ++ ")"
        schematize And []       = "∧"
        schematize Not (x:_)    = "¬" ++ x
        schematize Not []       = "¬"

instance UniformlyEq (BooleanConn b) where
        And =* And = True 
        Or  =* Or  = True 
        If  =* If  = True
        Iff =* Iff = True
        Not =* Not = True
        _ =* _ = False

instance Monad m => MaybeMonadVar (BooleanConn b) m

instance MaybeStaticVar (BooleanConn b)

instance FirstOrderLex (BooleanConn b)

data Modality b a where
        Box     :: Modality b (Form b -> Form b)
        Diamond :: Modality b (Form b -> Form b)

instance Schematizable (Modality b) where
        schematize Box = \(x:_) -> "□" ++ x
        schematize Diamond = \(x:_) -> "◇" ++ x

instance UniformlyEq (Modality b) where
         Box =* Box = True 
         Diamond =* Diamond = True 
         _ =* _ = False

instance Monad m => MaybeMonadVar (Modality b) m

instance MaybeStaticVar (Modality b)

instance FirstOrderLex (Modality b)

data IntConst b a where
        Constant :: Int -> IntConst b (Term b)

instance Schematizable (IntConst b) where
        schematize (Constant n)   _       
            | n < 0 && n > -6 = ["_abcde" !! (-1 * n)]
            | otherwise = "c_" ++ show n

instance UniformlyEq (IntConst b) where
        (Constant n) =* (Constant m) = n == m

instance Monad m => MaybeMonadVar (IntConst b) m

instance MaybeStaticVar (IntConst b)

instance FirstOrderLex (IntConst b) 

data StandardQuant b c a where
        All  :: String -> StandardQuant b c ((Term c -> Form b) -> Form b)
        Some :: String -> StandardQuant b c ((Term c -> Form b) -> Form b)

instance Schematizable (StandardQuant b c) where
        schematize (All v) = \(x:_) -> "∀" ++ v ++ x 
        schematize (Some v) = \(x:_) -> "∃" ++ v ++ x 

instance UniformlyEq (StandardQuant b c) where
        (All _) =* (All _) = True
        (Some _) =* (Some _) = True
        _ =* _ = False

instance Monad m => MaybeMonadVar (StandardQuant b c) m

instance MaybeStaticVar (StandardQuant b c)

instance FirstOrderLex (StandardQuant b c) 

data StandardVar b a where
    Var :: String -> StandardVar b (Term b)

instance Schematizable (StandardVar b) where
        schematize (Var s) = const s

instance UniformlyEq (StandardVar b) where
        (Var n) =* (Var m) = n == m

instance Monad m => MaybeMonadVar (StandardVar b) m

instance MaybeStaticVar (StandardVar b)

--Note that standard variables are 
instance FirstOrderLex (StandardVar b) 
