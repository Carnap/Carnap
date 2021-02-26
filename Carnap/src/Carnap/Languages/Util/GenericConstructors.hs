{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.Util.GenericConstructors where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes 
import Data.List (intercalate)

-----------------------
--  1. Propositions  --
-----------------------

data IntProp b a where
        Prop :: Int -> IntProp b (Form b)

instance Schematizable (IntProp b) where
        schematize (Prop n)   _ 
            | n >= 26 = (['A' .. 'Z'] !! (n `mod` 26)) : '_' : show (n `div` 26)
            | n >= 0 = [['A' .. 'Z'] !! n]
            | otherwise = "P_" ++ show n

instance UniformlyEq (IntProp b) where
        (Prop n) =* (Prop m) = n == m

instance FirstOrderLex (IntProp b) 

data SchematicIntProp b a where
        SProp :: Int -> SchematicIntProp b (Form b)

instance Schematizable (SchematicIntProp b) where
        schematize (SProp n)   _ 
            | n >= 14 && n <= 21 = ["ζφψχθγξ" !! (n - 14)]
            | n >= 0 = ("ζφψχθγξ" !! (n `mod` 7)) : '_' : show (n `div` 7)
            | otherwise = "φ_" ++ show n

instance UniformlyEq (SchematicIntProp b) where
        (SProp n) =* (SProp m) = n == m

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
        Pred ::  Arity (Term c) (Form b) ret -> Int -> IntPred b c ret

instance Schematizable (IntPred b c) where
        schematize (Pred a n) xs = pred ++ tail 
            where arity = arityInt a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | n >= 26 = (['A' .. 'Z'] !! (n `mod` 26)) : '_' : show (n `div` 26)
                    | n >= 0 = [['A' .. 'Z'] !! n]
                    | otherwise  = "F_" ++ show n
                  tail
                    | arity == 0    = ""
                    | otherwise     = "(" ++ intercalate "," args ++ ")"

instance UniformlyEq (IntPred b c) where
        (Pred a n) =* (Pred a' m) = show a == show a' && n == m

instance FirstOrderLex (IntPred b c)

data StringPred b c a where
        StringPred ::  Arity (Term c) (Form b) ret -> String -> StringPred b c ret

instance Schematizable (StringPred b c) where
        schematize (StringPred a pred) xs = pred ++ tail 
            where arity = arityInt a
                  args = take arity $ xs ++ repeat "_"
                  tail
                    | arity == 0    = ""
                    | otherwise     = "(" ++ intercalate "," args ++ ")"

instance UniformlyEq (StringPred b c) where
        (StringPred a s) =* (StringPred a' s') = show a == show a' && s == s'

instance FirstOrderLex (StringPred b c)

data SchematicIntPred b c a where
        SPred :: Arity (Term c) (Form b) ret -> Int -> SchematicIntPred b c ret

instance Schematizable (SchematicIntPred b c) where
        schematize (SPred a n) xs = pred ++ tail
            where arity = read $ show a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | n >= 0 && n <= 7 = ["ξθγζϚφψχ" !! n]
                    | n >= 0 = ("ξθγζϚφψχ" !! (n `mod` 8)) : '_' : show (n `div` 8)
                    | otherwise = "φ_" ++ show n 
                  tail
                    | arity == 0 = ""
                    | otherwise = "(" ++ intercalate "," args ++ ")"

instance UniformlyEq (SchematicIntPred b c) where
        (SPred a n) =* (SPred a' m) = show a == show a' && n == m

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

instance FirstOrderLex (TermEq c b)

data TermElem c b a where
        TermElem :: TermElem c b (Term b -> Term b -> Form c)

instance Schematizable (TermElem c b) where
        schematize TermElem = \(t1:t2:_) -> t1 ++ "∈" ++ t2

instance UniformlyEq (TermElem c b) where
        _ =* _ = True

instance FirstOrderLex (TermElem c b)

data TermSubset c b a where
        TermSubset :: TermSubset c b (Term b -> Term b -> Form c)

instance Schematizable (TermSubset c b) where
        schematize TermSubset = \(t1:t2:_) -> t1 ++ "⊆" ++ t2

instance UniformlyEq (TermSubset c b) where
        _ =* _ = True

instance FirstOrderLex (TermSubset c b)

data TermLessThan c b a where
        TermLessThan :: TermLessThan c b (Term b -> Term b -> Form c)

instance Schematizable (TermLessThan c b) where
        schematize TermLessThan = \(t1:t2:_) -> t1 ++ "<" ++ t2

instance UniformlyEq (TermLessThan c b) where
        _ =* _ = True

instance FirstOrderLex (TermLessThan c b)

---------------------------
--  3. Function Symbols  --
---------------------------

data IntFunc c b a where
        Func ::  Arity (Term c) (Term b) ret -> Int -> IntFunc b c ret

instance Schematizable (IntFunc b c) where
        schematize (Func a n) xs = pred ++ tail 
            where arity = arityInt a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | n >= 26 = (['a' .. 'z'] !! (n `mod` 26)) : '_' : show (n `div` 26)
                    | n >= 0 = [['a' .. 'z'] !! n]
                    | otherwise  = "f_" ++ show n 
                  tail
                    | arity == 0    = ""
                    | otherwise     = "(" ++ intercalate "," args ++ ")"

instance UniformlyEq (IntFunc b c) where
        (Func a n) =* (Func a' m) = show a == show a' && n == m

instance FirstOrderLex (IntFunc b c)

data StringFunc c b a where
        StringFunc ::  Arity (Term c) (Term b) ret -> String -> StringFunc b c ret

instance Schematizable (StringFunc b c) where
        schematize (StringFunc a pred) xs = pred ++ tail 
            where arity = arityInt a
                  args = take arity $ xs ++ repeat "_"
                  tail
                    | arity == 0    = ""
                    | otherwise     = "(" ++ intercalate "," args ++ ")"

instance UniformlyEq (StringFunc b c) where
        (StringFunc a s) =* (StringFunc a' s') = show a == show a' && s == s'

instance FirstOrderLex (StringFunc b c)

data SchematicIntFunc c b a where
        SFunc ::  Arity (Term c) (Term b) ret -> Int -> SchematicIntFunc b c ret

instance Schematizable (SchematicIntFunc b c) where
        schematize (SFunc a n) xs = pred ++ tail
            where arity = read $ show a
                  args = take arity $ xs ++ repeat "_"
                  pred 
                    | arity == 0 && n >= 3 = ("τπμ" !! (n `mod` 3)) : '_' : show (n `div` 3)
                    | arity == 0 && n >= 0 = ["τπμ" !! n]
                    | n >= 5 && n <= 9 = ["τνυρκ" !! (n - 5)]
                    | n >= 0 = ("τνυρκ" !! (n `mod` 5)) : '_' : show (n `div` 5)
                    | otherwise  = "τ_" ++ show n 
                  tail
                    | arity == 0    = ""
                    | otherwise     = "(" ++ intercalate "," args ++ ")"


instance UniformlyEq (SchematicIntFunc b c) where
        (SFunc a n) =* (SFunc a' m) = show a == show a' && n == m

instance FirstOrderLex (SchematicIntFunc b c) where
        isVarLex _ = True

data ElementarySetOperations b a where
        Intersection :: ElementarySetOperations b (Term b -> Term b -> Term b)
        Union :: ElementarySetOperations b (Term b -> Term b -> Term b)
        RelComplement :: ElementarySetOperations b (Term b -> Term b -> Term b)
        Powerset :: ElementarySetOperations b (Term b -> Term b)
        EmptySet :: ElementarySetOperations b (Term b)

instance Schematizable (ElementarySetOperations b) where
        schematize Intersection (x:y:_)  = "(" ++ x ++ "∩" ++ y ++ ")"
        schematize Intersection _       = "∩"
        schematize Union (x:y:_)  = "(" ++ x ++ "∪" ++ y ++ ")"
        schematize Union _       = "∪"
        schematize RelComplement (x:y:_)  = "(" ++ x ++ "/" ++ y ++ ")"
        schematize RelComplement _       = "\\"
        schematize Powerset (x:_)  = "Pow(" ++ x ++ ")"
        schematize Powerset _  = "Pow"
        schematize EmptySet _  = "∅"

instance UniformlyEq (ElementarySetOperations b) where
        Intersection =* Intersection = True 
        Union =* Union = True 
        RelComplement =* RelComplement = True
        Powerset =* Powerset = True
        EmptySet =* EmptySet = True
        _ =* _ = False

instance FirstOrderLex (ElementarySetOperations b)

data ElementaryArithmeticOperations b a where 
        ArithAddition :: ElementaryArithmeticOperations b (Term b -> Term b -> Term b)
        ArithMultiplication :: ElementaryArithmeticOperations b (Term b -> Term b -> Term b)
        ArithSuccessor :: ElementaryArithmeticOperations b (Term b -> Term b)
        ArithZero :: ElementaryArithmeticOperations b (Term b)

instance Schematizable (ElementaryArithmeticOperations b) where
        schematize ArithAddition (x:y:_)  = "(" ++ x ++ "+" ++ y ++ ")"
        schematize ArithAddition _       = "+"
        schematize ArithMultiplication (x:y:_)  = "(" ++ x ++ "×" ++ y ++ ")"
        schematize ArithMultiplication _       = "×"
        schematize ArithSuccessor (x:_)  =  x ++ "'"
        schematize ArithSuccessor _       = "'"
        schematize ArithZero _  = "0"

instance UniformlyEq (ElementaryArithmeticOperations b) where
        ArithAddition =* ArithAddition = True 
        ArithMultiplication =* ArithMultiplication = True 
        ArithSuccessor =* ArithSuccessor = True
        ArithZero =* ArithZero = True
        _ =* _ = False

instance FirstOrderLex (ElementaryArithmeticOperations b)

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

instance FirstOrderLex (Modality b)

data GenericContext b c a where
        Context :: Int -> GenericContext b c (Form b -> Form c)

instance Schematizable (GenericContext b c) where
        schematize (Context n) (x:_)  = "Φ_" ++ show n ++ "(" ++ x ++ ")"

instance UniformlyEq (GenericContext b c) where
        (Context n) =* (Context m) = n == m

instance FirstOrderLex (GenericContext b c) where
        isVarLex _ = True

type PropositionalContext b = GenericContext b b

----------------
--  5. Terms  --
----------------

data IntConst b a where
        Constant :: Int -> IntConst b (Term b)

instance Schematizable (IntConst b) where
        schematize (Constant n)   _       
            | n >= 26 = (['a' .. 'z'] !! (n `mod` 26)) : '_' : show (n `div` 26)
            | n >= 0 = [['a' .. 'z'] !! n]
            | otherwise = "c_" ++ show n

instance UniformlyEq (IntConst b) where
        (Constant n) =* (Constant m) = n == m

instance FirstOrderLex (IntConst b) 

data StandardVar b a where
    Var :: String -> StandardVar b (Term b)

instance Schematizable (StandardVar b) where
        schematize (Var s) = const s

instance UniformlyEq (StandardVar b) where
        (Var n) =* (Var m) = n == m

-- XXX Note: standard variables are not schematic variables
instance FirstOrderLex (StandardVar b) 

data IntIndex b a where
        Index :: Int -> IntIndex b (Term b)

instance Schematizable (IntIndex b) where
        schematize (Index n) _ = show n

instance UniformlyEq (IntIndex b) where
        (Index n) =* (Index m) = n == m

instance FirstOrderLex (IntIndex b)

data PolyVar c b a where
        PolyVar :: String -> Arity c b t -> PolyVar c b (Form t)

instance Schematizable (PolyVar c b) where
        schematize (PolyVar s a) = const s

instance UniformlyEq (PolyVar c b) where
    (PolyVar n a) =* (PolyVar m a') = n == m && show a == show a'

instance FirstOrderLex (PolyVar c b)

----------------------
--  6. Binders      --
----------------------

data RescopingOperator f g b c :: (* -> *) -> * -> * where
        Rescope :: String -> RescopingOperator f g b c lang (f b -> (f b -> g c) -> g c)

instance UniformlyEq (RescopingOperator f g b c lang) where
    (Rescope _) =* (Rescope _) = True

instance FirstOrderLex (RescopingOperator f g b c lang) 

instance Schematizable (RescopingOperator f g b c lang) where
        schematize (Rescope v)  = \(t:f:_) -> "(" ++ t ++ "/" ++ v ++ ")" ++ f

type ScopedTermOperator  = RescopingOperator Term Form

data DefiniteDescription b c a where
        DefinDesc :: String -> DefiniteDescription b c ((Term c -> Form b) -> Term c)

instance Schematizable (DefiniteDescription b c) where
        schematize (DefinDesc v) = \(x:_) -> "℩" ++ v ++ x 

instance UniformlyEq (DefiniteDescription b c) where
        (DefinDesc _) =* (DefinDesc _) = True

instance FirstOrderLex (DefiniteDescription b c) 

data GenericTypedLambda f g b a where
        TypedLambda :: String -> GenericTypedLambda f g b ((f b -> g c) -> g (b -> c))

instance UniformlyEq (GenericTypedLambda f g b) where
    (TypedLambda _) =* (TypedLambda _) = True

instance FirstOrderLex (GenericTypedLambda f g b) 

instance Schematizable (GenericTypedLambda f g b) where
        schematize (TypedLambda v)  = \(x:_) -> if last x == ']' then "λ" ++ v ++ x
                                                                        else "λ" ++ v ++ "[" ++ x ++ "]"

type SOLambda = GenericTypedLambda Term Form Int

data GenericQuant f g b c a where
        All  :: String -> GenericQuant f g b c ((f c -> g b) -> g b)
        Some :: String -> GenericQuant f g b c ((f c -> g b) -> g b)

type StandardQuant = GenericQuant Term Form

instance Schematizable (GenericQuant f g b c) where
        schematize (All v) (x:_) = "∀" ++ v ++ x 
        schematize (All v) [] = "∀" ++ v
        schematize (Some v) (x:_) = "∃" ++ v ++ x 
        schematize (Some v) [] = "∃" ++ v

instance UniformlyEq (GenericQuant f g b c) where
        (All _) =* (All _) = True
        (Some _) =* (Some _) = True
        _ =* _ = False

instance FirstOrderLex (GenericQuant f g b c) 

data QuantifiedContext b c :: (* -> *) -> * -> * where
        QuantContext :: Int -> Arity (Term c) (Form b) ret -> QuantifiedContext b c lang (ret -> Form b)

instance Schematizable (QuantifiedContext b c lang) where
        schematize (QuantContext n a) (x:_)  = "Ψ^" ++ show a ++ "_" ++ show n ++ "(" ++ x ++ ")"
        schematize (QuantContext n a) []  = "Ψ^" ++ show a ++ "_" ++ show n

instance UniformlyEq (QuantifiedContext b c lang) where
        (QuantContext n a) =* (QuantContext m a') = n == m && show a == show a'

instance ReLex (QuantifiedContext b c) where
        relex (QuantContext n a) = QuantContext n a

instance FirstOrderLex (QuantifiedContext b c lang) where
        isVarLex _ = True

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

instance FirstOrderLex (Accessor c b)

data Separation b c :: (* -> *) -> * -> * where
        Separation :: String -> Separation b c lang (Term b -> (Term b -> Form c) -> Term b)

instance Schematizable (Separation b c lang) where
        schematize (Separation v) (t:f:xs) = concat ["{",v,"∈",t,"|", f,"}"]
                  -- XXX Quick and dirty fix for display issue. Should
                  -- actually make this dependent on the presence of
                  -- some kind of variable constructor in the language

        schematize (Separation v) _ = "{|}"

instance UniformlyEq (Separation b c lang) where
        _ =* _ = True

instance FirstOrderLex (Separation b c lang)

instance ReLex (Separation b c) where
        relex (Separation v) = (Separation v)
