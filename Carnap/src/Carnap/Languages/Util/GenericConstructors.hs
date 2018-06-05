{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.Util.GenericConstructors where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses 
import Data.List (intercalate)

-----------------------
--  1. Propositions  --
-----------------------

data IntProp b a where
        Prop :: Int -> IntProp b (Form b)

instance Schematizable (IntProp b) where
        schematize (Prop n)   _ 
            | n < 0 && n > -27 = ["_ABCDEFGHIJKLMNOPQRSTUVWXYZ" !! (-1 * n)]
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
            | n < -15 && n > -23 = ["_φψχθγζξ" !! (-1 * (n + 15))]
            | otherwise = "φ_" ++ show n

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

---------------------
--  2. Predicates  --
---------------------

data IntPred b c a where
        Pred ::  Arity (Term c) (Form b) n ret -> Int -> IntPred b c ret

instance Schematizable (IntPred b c) where
        schematize (Pred a n) xs = pred ++ tail 
            where arity = read $ show a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | n < 0 && n > -27 = ["_ABCDEFGHIJKLMNOPQRSTUVWXYZ" !! (-1 * n)]
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

data TermEq c b a where
        TermEq :: TermEq c b (Term b -> Term b -> Form c)

instance Schematizable (TermEq c b) where
        schematize TermEq = \(t1:t2:_) -> t1 ++ "=" ++ t2

instance UniformlyEq (TermEq c b) where
        _ =* _ = True

instance Monad m => MaybeMonadVar (TermEq c b) m

instance MaybeStaticVar (TermEq c b)

instance FirstOrderLex (TermEq c b)

data TermElem c b a where
        TermElem :: TermElem c b (Term b -> Term b -> Form c)

instance Schematizable (TermElem c b) where
        schematize TermElem = \(t1:t2:_) -> t1 ++ "∈" ++ t2

instance UniformlyEq (TermElem c b) where
        _ =* _ = True

instance Monad m => MaybeMonadVar (TermElem c b) m

instance MaybeStaticVar (TermElem c b)

instance FirstOrderLex (TermElem c b)

data TermSubset c b a where
        TermSubset :: TermSubset c b (Term b -> Term b -> Form c)

instance Schematizable (TermSubset c b) where
        schematize TermSubset = \(t1:t2:_) -> t1 ++ "⊆" ++ t2

instance UniformlyEq (TermSubset c b) where
        _ =* _ = True

instance Monad m => MaybeMonadVar (TermSubset c b) m

instance MaybeStaticVar (TermSubset c b)

instance FirstOrderLex (TermSubset c b)

---------------------------
--  3. Function Symbols  --
---------------------------

data IntFunc c b a where
        Func ::  Arity (Term c) (Term b) n ret -> Int -> IntFunc b c ret

instance Schematizable (IntFunc b c) where
        schematize (Func a n) xs = pred ++ tail 
            where arity = read $ show a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | n < 0 && n > -27 = ["_abcdefghijklmnopqrstuvwxyz" !! (-1 * n)]
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

data ElementarySetOperations b a where
        Intersection :: ElementarySetOperations b (Term b -> Term b -> Term b)
        Union :: ElementarySetOperations b (Term b -> Term b -> Term b)
        RelComplement :: ElementarySetOperations b (Term b -> Term b -> Term b)
        Powerset :: ElementarySetOperations b (Term b -> Term b)

instance Schematizable (ElementarySetOperations b) where
        schematize Intersection (x:y:_)  = "(" ++ x ++ "∩" ++ y ++ ")"
        schematize Intersection _       = "∩"
        schematize Union (x:y:_)  = "(" ++ x ++ "∪" ++ y ++ ")"
        schematize Union _       = "∪"
        schematize RelComplement (x:y:_)  = "(" ++ x ++ "/" ++ y ++ ")"
        schematize RelComplement _       = "/"
        schematize Powerset (x:_)  = "Pow(" ++ x ++ ")"
        schematize Powerset _  = "Pow"

instance UniformlyEq (ElementarySetOperations b) where
        Intersection =* Intersection = True 
        Union =* Union = True 
        RelComplement =* RelComplement = True
        Powerset =* Powerset = True
        _ =* _ = False

instance Monad m => MaybeMonadVar (ElementarySetOperations b) m

instance MaybeStaticVar (ElementarySetOperations b)

instance FirstOrderLex (ElementarySetOperations b)

----------------------
--  4. Connectives  --
----------------------

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

data BooleanConst b a where
        Verum :: BooleanConst b (Form b)
        Falsum :: BooleanConst b (Form b)

instance Schematizable (BooleanConst b) where
        schematize Verum  _  = "⊤"
        schematize Falsum _  = "⊥"

instance UniformlyEq (BooleanConst b) where
        Verum =* Verum = True 
        Falsum =* Falsum = True 
        _ =* _ = False

instance Monad m => MaybeMonadVar (BooleanConst b) m

instance MaybeStaticVar (BooleanConst b)

instance FirstOrderLex (BooleanConst b)

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

data PropositionalContext b a where
        PropCtx :: Int -> PropositionalContext b (Form b -> Form b)

instance Schematizable (PropositionalContext b) where
        schematize (PropCtx n) (x:_)  = "Φ_" ++ show n ++ "(" ++ x ++ ")"

instance UniformlyEq (PropositionalContext b) where
        (PropCtx n) =* (PropCtx m) = n == m

instance Monad m => MaybeMonadVar (PropositionalContext b) m

instance MaybeStaticVar (PropositionalContext b)

instance FirstOrderLex (PropositionalContext b) where
        isVarLex _ = True

----------------
--  5. Terms  --
----------------

data IntConst b a where
        Constant :: Int -> IntConst b (Term b)

instance Schematizable (IntConst b) where
        schematize (Constant n)   _       
            | n < 0 && n > -27 = ["_abcdefghijklmnopqrstuvwxyz" !! (-1 * n)]
            | otherwise = "c_" ++ show n

instance UniformlyEq (IntConst b) where
        (Constant n) =* (Constant m) = n == m

instance Monad m => MaybeMonadVar (IntConst b) m

instance MaybeStaticVar (IntConst b)

instance FirstOrderLex (IntConst b) 

data StandardVar b a where
    Var :: String -> StandardVar b (Term b)

instance Schematizable (StandardVar b) where
        schematize (Var s) = const s

instance UniformlyEq (StandardVar b) where
        (Var n) =* (Var m) = n == m

instance Monad m => MaybeMonadVar (StandardVar b) m

instance MaybeStaticVar (StandardVar b)

-- XXX Note: standard variables are not schematic variables
instance FirstOrderLex (StandardVar b) 

data IntIndex b a where
        Index :: Int -> IntIndex b (Term b)

instance Schematizable (IntIndex b) where
        schematize (Index n) _ = show n

instance UniformlyEq (IntIndex b) where
        (Index n) =* (Index m) = n == m

instance Monad m => MaybeMonadVar (IntIndex b) m

instance MaybeStaticVar (IntIndex b)

instance FirstOrderLex (IntIndex b)


----------------------
--  6. Quantifiers  --
----------------------

data GenericQuant f g b c a where
        All  :: String -> GenericQuant f g b c ((f c -> g b) -> g b)
        Some :: String -> GenericQuant f g b c ((f c -> g b) -> g b)

type StandardQuant = GenericQuant Term Form

instance Schematizable (GenericQuant f g b c) where
        schematize (All v) = \(x:_) -> "∀" ++ v ++ x 
        schematize (Some v) = \(x:_) -> "∃" ++ v ++ x 

instance UniformlyEq (GenericQuant f g b c) where
        (All _) =* (All _) = True
        (Some _) =* (Some _) = True
        _ =* _ = False

instance Monad m => MaybeMonadVar (GenericQuant f g b c) m

instance MaybeStaticVar (GenericQuant f g b c)

instance FirstOrderLex (GenericQuant f g b c) 

------------------
--  7. Exotica  --
------------------

data Indexer a b c :: (* -> *) -> * -> * where
        AtIndex :: Indexer a b c lang (Form b -> Term a -> Form c)

instance FirstOrderLex (Indexer a b c lang)

instance UniformlyEq (Indexer a b c lang) where
        AtIndex =* AtIndex = True

instance Schematizable (Indexer a b c lang) where
        schematize AtIndex = \(x:y:_) -> "(" ++ x ++ "/" ++ y ++ ")"

instance ReLex (Indexer a b c) where
        relex AtIndex = AtIndex

data Cons b a where
        Cons :: Cons b (Term b -> Term b -> Term b)

instance Schematizable (Cons b) where
        schematize Cons = \(x:y:_) -> x ++ "-" ++ y

instance FirstOrderLex (Cons b)

instance UniformlyEq (Cons b) where
        Cons =* Cons = True

data Accessor c b a where
        Accesses :: Accessor c b (Term b -> Term b -> Form c)

instance Schematizable (Accessor c b) where
        schematize Accesses = \(t1:t2:_) -> t1 ++ "≺" ++ t2

instance UniformlyEq (Accessor c b) where
        _ =* _ = True

instance Monad m => MaybeMonadVar (Accessor c b) m

instance MaybeStaticVar (Accessor c b)

instance FirstOrderLex (Accessor c b)

data Separation b c :: (* -> *) -> * -> * where
        Separation :: String -> Separation b c lang (Term b -> (Term b -> Form c) -> Term b)

instance Schematizable (Separation b c lang) where
        schematize (Separation v) (t:f:xs) = concat ["{",v,"∈",t,"|",f,"}"]
        schematize (Separation v) _ = "{|}"

instance UniformlyEq (Separation b c lang) where
        _ =* _ = True

instance Monad m => MaybeMonadVar (Separation b c lang) m

instance MaybeStaticVar (Separation b c lang)

instance FirstOrderLex (Separation b c lang)
