{-#LANGUAGE TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, ScopedTypeVariables, AutoDeriveTypeable, DefaultSignatures #-}

module Carnap.Core.Data.AbstractSyntaxDataTypes(
  CopulaSchema(..),
  BoundVars(..),
  -- * Abstract Types
  -- $ATintro
  -- ** Language Building Types
  Term(..), Form(..), 
  Copula((:$:), Lam), (:|:)(..), Fix(Fx), FixLang, EndLang, pattern AOne,
  pattern ATwo, pattern AThree, pattern LLam, pattern (:!$:), pattern Fx1,
  pattern Fx2, pattern Fx3, pattern Fx4, pattern Fx5, pattern Fx6, pattern
  Fx7, pattern Fx8, pattern Fx9, pattern Fx10, pattern Fx11, pattern Lx1,
  pattern Lx2, pattern Lx3, pattern Lx4, pattern Lx5, pattern Lx6, pattern
  Lx7, pattern Lx8, pattern Lx9, pattern Lx10, pattern Lx11, pattern FX,
  -- ** Abstract Term Types
  -- *** Variable Binding Operators
  Quantifiers(Bind),Abstractors(Abstract),Applicators(Apply), 
  -- *** Non-Binding Operators 
  Arity(AZero, ASucc), 
  Predicate(Predicate), 
  Connective(Connective), Function(Function), 
  Subnective(Subnective),
  SubstitutionalVariable(SubVar),  
  LangTypes2(..), LangTypes1(..), RelabelVars(..),   
  FirstOrderLex(..),
) where

import Carnap.Core.Util
import Data.Typeable
import Carnap.Core.Unification.Unification
import Control.Lens
import Carnap.Core.Data.AbstractSyntaxClasses
import qualified Control.Monad.State.Lazy as S

--This module attempts to provide abstract syntax types that would cover
--a wide variety of languages


class FirstOrderLex f where
    isVarLex :: f a -> Bool
    isVarLex _ = False
    sameHeadLex :: f a -> f b -> Bool
    -- decomposeLex :: f a -> f a -> [Equation f]
    --we'll work on this at the fixed point.
    --
    --occursLex :: f idx a -> f idx b -> Bool
    --
    --unless we're dealing with a fixed point, we only substitute at the
    --top level with this function
    --substLex :: f a -> f c -> f b -> f b
    freshVarsLex :: Typeable a => Maybe [f a]
    freshVarsLex = Nothing

--------------------------------------------------------
--2. Abstract Types
--------------------------------------------------------

-- $ATintro
-- Here are some types for abstract syntax. The basic proposal
-- is that we only define how terms of different types connect
-- and let the user define all the connections independently of
-- of their subparts. In some sense they just define the type
-- and the type system figures out how they can go together

-- We use the idea of a semantic value to indicate approximately a Fregean
-- sense, or intension: approximately a function from models to Fregean
-- denotations in those models

--------------------------------------------------------
--2.1 Language Building Types
--------------------------------------------------------

{-|
This is the type that describes how things are connected.
Things are connected either by application or by
a lambda abstraction. The 'lang' parameter gets fixed to
form a fully usable type

@
   Fix (Copula :|: Copula :|: (Predicate BasicProp :|: Connective BasicConn))
@
-}
data Copula lang t where
    (:$:) :: (Typeable t, Typeable t') => lang (t -> t') -> lang t -> Copula lang t'
    Lam :: (Typeable t, Typeable t') => (lang t -> lang t') -> Copula lang (t -> t')
    Lift :: t -> Copula lang t

class CopulaSchema lang where
    appSchema :: lang (t -> t') -> lang t -> [String] -> String
    default appSchema :: (Schematizable lang, Show (lang t)) => lang (t -> t') -> lang t -> [String] -> String
    appSchema x y e = schematize x (show y : e)
    liftSchema :: Copula lang t -> [String] -> String
    lamSchema = error "how did you even do this?"
    lamSchema :: (lang t -> lang t') -> [String] -> String
    liftSchema = error "should not print a lifted value"

{-|
this is type acts a disjoint sum/union of two functors
it carries though the phantom type as well
-}
data (:|:) :: (k -> k' -> *) -> (k -> k' -> *) -> k -> k' -> * where
    FLeft :: f x idx -> (f :|: g) x idx
    FRight :: g x idx -> (f :|: g) x idx

infixr 5 :|:

-- | This type fixes the first argument of a functor and carries though a
-- | phantom type. note that only certian kinds of functors even have a kind
-- | such that the first argument is fixable
data Fix f idx where
    Fx ::  Typeable idx => f (Fix f) idx -> Fix f idx

-- | This is an empty abstract type, which can be used to close off
-- | a series of applications of `:|:`, so that the right-most leaf
-- | doesn't need special treatment.
data EndLang :: (* -> *) -> * -> *

type FixLang f = Fix (Copula :|: f)

pattern (:!$:) f x = Fx (FLeft  (f :$: x))
pattern LLam f     = Fx (FLeft  (Lam f))
pattern Lx1 x      = FLeft x
pattern Lx2 x      = FRight (FLeft x)
pattern Lx3 x      = FRight (FRight (FLeft x))
pattern Lx4 x      = FRight (FRight (FRight (FLeft x)))
pattern Lx5 x      = FRight (FRight (FRight (FRight (FLeft x))))
pattern Lx6 x      = FRight (FRight (FRight (FRight (FRight (FLeft x)))))
pattern Lx7 x      = FRight (FRight (FRight (FRight (FRight (FRight (FLeft x))))))
pattern Lx8 x      = FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x)))))))
pattern Lx9 x      = FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x))))))))
pattern Lx10 x     = FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x)))))))))
pattern Lx11 x     = FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x))))))))))
pattern Lx12 x     = FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x)))))))))))
pattern Fx1 x      = FX (Lx1  x) 
pattern Fx2 x      = FX (Lx2  x)
pattern Fx3 x      = FX (Lx3  x)
pattern Fx4 x      = FX (Lx4  x)
pattern Fx5 x      = FX (Lx5  x)
pattern Fx6 x      = FX (Lx6  x)
pattern Fx7 x      = FX (Lx7  x)
pattern Fx8 x      = FX (Lx8  x)
pattern Fx9 x      = FX (Lx9  x)
pattern Fx10 x     = FX (Lx10 x)
pattern Fx11 x     = FX (Lx11 x)
pattern Fx12 x     = FX (Lx12 x)
pattern FX x = Fx (FRight x)

--------------------------------------------------------
--2.2 Abstract Operator Types 
--------------------------------------------------------

--------------------------------------------------------
--2.2.1 Variable Binding Operators
--------------------------------------------------------

data Quantifiers :: (* -> *) -> (* -> *) -> * -> * where
    Bind :: quant ((t a -> f b) -> f b) -> Quantifiers quant lang ((t a -> f b) -> f b)

data Abstractors :: (* -> *) -> (* -> *) -> * -> * where
    Abstract :: abs ((t a -> t b) -> t (a -> b)) -> Abstractors abs lang ((t a -> t b) -> t (a -> b))

data Applicators :: (* -> *) -> (* -> *) -> * -> * where
    Apply :: app (t (a -> b) -> t a -> t b) -> Applicators app lang (t (a -> b) -> t a -> t b)

{-|
This typeclass needs to provide a way of getting bound variables,
which will display binding positions, a way of substituting bound
variables, and a way of getting a bound variable uniquely determined by
the "Height" of a certain binder---how many binders occur below it in
a parsing tree.
-}
class BoundVars g where
        getBoundVar :: Typeable a => FixLang g ((a -> b) -> c) -> FixLang g (a -> b) -> FixLang g a
        getBoundVar = error "you need to define a language-specific getBoundVar function"
        subBoundVar :: FixLang g a -> FixLang g a -> FixLang g b -> FixLang g b
        subBoundVar _ _ = id
        getBindHeight:: Typeable a => FixLang g ((a -> b) -> c) -> FixLang g (a -> b) -> FixLang g a
        getBindHeight = error "you need to define a language-specific getBindHeight function"

data Term a = Term a
    deriving(Eq, Ord, Show)

instance Evaluable Term where
    eval (Term x) = x

instance Liftable Term where
    lift = Term

data Form a = Form a
    deriving(Eq, Ord, Show)

instance Evaluable Form where
    eval (Form x) = x

instance Liftable Form where
    lift = Form

--------------------------------------------------------
--2.2.2 Non-Binding Operators
--------------------------------------------------------

-- | think of this as a type constraint. the lang type, model type, and number
-- | must all match up for this type to be inhabited
-- | this lets us do neat type safty things
data Arity :: * -> * -> Nat -> * -> * where
    AZero :: Arity arg ret Zero ret
    ASucc :: Arity arg ret n ret' -> Arity arg ret (Succ n) (arg -> ret')

pattern AOne = ASucc AZero
pattern ATwo = ASucc AOne
pattern AThree = ASucc ATwo

arityInt :: Arity arg ret n ret' -> Int
arityInt AZero = 0
arityInt (ASucc n) = arityInt n + 1

instance Show (Arity arg ret n ret') where
        show = show . arityInt

data Predicate :: (* -> *) -> (* -> *) -> * -> * where
    Predicate :: pred t -> Arity (Term a) (Form b) n t -> Predicate pred lang t

data Connective :: (* -> *) -> (* -> *) -> * -> * where
    Connective :: con t -> Arity (Form a) (Form b) n t -> Connective con lang t

data Function :: (* -> *) -> (* -> *) -> * -> * where
    Function :: func t -> Arity (Term a) (Term b) n t -> Function func lang t

data Subnective :: (* -> *) -> (* -> *) -> * -> * where
    Subnective :: sub t -> Arity (Form a) (Term b) n t -> Subnective sub lang t

data SubstitutionalVariable :: (* -> *) -> * -> * where
        SubVar :: Int -> SubstitutionalVariable lang t

--data Quote :: (* -> *) -> * -> *
    --Quote :: (lang )
--------------------------------------------------------
--3. Schematizable, Show, and Eq
--------------------------------------------------------

instance Schematizable (SubstitutionalVariable lang)  where
        schematize (SubVar n) = const $ "α_" ++ show n

--dummy instance for a type with no constructors
instance Schematizable (EndLang lang) where
        schematize = undefined

instance (Schematizable (f a), Schematizable (g a)) => Schematizable ((f :|: g) a) where
        schematize (FLeft a) = schematize a
        schematize (FRight a) = schematize a

instance Schematizable (f (Fix f)) => Schematizable (Fix f) where
    schematize (Fx a) = schematize a

instance Schematizable quant => Schematizable (Quantifiers quant lang) where
        schematize (Bind q) arg = schematize q arg --here I assume 'q' stores the users varible name

instance Schematizable abs => Schematizable (Abstractors abs lang) where
        schematize (Abstract a) arg = schematize a arg --here I assume 'q' stores the users varible name

instance Schematizable pred => Schematizable (Predicate pred lang) where
        schematize (Predicate p _) = schematize p

instance Schematizable con => Schematizable (Connective con lang) where
        schematize (Connective c _) = schematize c

instance Schematizable func => Schematizable (Function func lang) where
        schematize (Function f _) = schematize f

instance Schematizable app => Schematizable (Applicators app lang) where
        schematize (Apply f) = schematize f

instance Schematizable sub => Schematizable (Subnective sub lang) where
        schematize (Subnective s _) = schematize s

instance CopulaSchema lang => Schematizable (Copula lang) where
        schematize (f :$: x) e = appSchema f x e
        schematize (Lam f)   e = lamSchema f e
        schematize x         e = liftSchema x e

instance (Schematizable (f a), Schematizable (g a)) => Show ((f :|: g) a b) where
        show (FLeft a) = schematize a []
        show (FRight a) = schematize a []

instance Schematizable (f (Fix f)) => Show (Fix f idx) where
        show (Fx a) = schematize a []

instance Schematizable quant => Show (Quantifiers quant lang a) where
        show x = schematize x []

instance Schematizable pred => Show (Predicate pred lang a) where
        show x = schematize x []

instance Schematizable con => Show (Connective con lang a) where
        show x = schematize x []

instance Schematizable func => Show (Function func lang a) where
        show x = schematize x []

instance Schematizable sub => Show (Subnective sub lang a) where
        show x = schematize x []

--instance -# OVERLAPPING #- Schematizable ((Copula :|: f1) a) => Eq ((Copula :|: f1) a b) where
        --x == y = show x == show y

instance Schematizable quant => Eq (Quantifiers quant lang a) where
        x == y = show x == show y

instance Schematizable pred => Eq (Predicate pred lang a) where
        x == y = show x == show y

instance Schematizable con => Eq (Connective con lang a) where
        x == y = show x == show y

instance Schematizable func => Eq (Function func lang a) where
        x == y = show x == show y

instance Schematizable sub => Eq (Subnective sub lang a) where
        x == y = show x == show y

instance (Schematizable (f a), Schematizable (g a)) => Eq ((f :|: g) a b) where
        x == y = show x == show y

instance  (CanonicalForm (FixLang f a), Show (FixLang f a)) => Eq (FixLang f a) where
        x == y = show (canonical x) == show (canonical y)

--}

--------------------------------------------------------
--4. Evaluation and Modelable
--------------------------------------------------------
instance Evaluable (SubstitutionalVariable lang)  where
        eval _ = error "It should not be possible to evaluate a substitutional variable"

instance Evaluable quant => Evaluable (Quantifiers quant lang) where
    eval (Bind q) = eval q

instance Evaluable abs => Evaluable (Abstractors abs lang) where
    eval (Abstract a) = eval a

instance Evaluable pred => Evaluable (Predicate pred lang) where
    eval (Predicate p a) = eval p

instance Evaluable con => Evaluable (Connective con lang) where
    eval (Connective p a) = eval p

instance Evaluable func => Evaluable (Function func lang) where
    eval (Function p _) = eval p

instance Evaluable app => Evaluable (Applicators app lang) where
    eval (Apply f) = eval f

instance Evaluable sub => Evaluable (Subnective sub lang) where
    eval (Subnective p a) = eval p

--dummy instance for a type with no constructors
instance Evaluable (EndLang lang) where
        eval = undefined

instance (Evaluable (f lang), Evaluable (g lang)) => Evaluable ((f :|: g) lang) where
    eval (FLeft p) = eval p
    eval (FRight p) = eval p

instance (Evaluable (f (Fix f))) => Evaluable (Fix f) where
    eval (Fx a) = eval a

instance Liftable (Fix (Copula :|: a)) where
    lift a = Fx $ FLeft (Lift a)

instance (Liftable lang, Evaluable lang) => Evaluable (Copula lang) where
    eval (f :$: x) = eval f (eval x)
    eval (Lam f)   = \t -> eval $ f (lift t)
    eval (Lift t)  = t

instance Modelable a (SubstitutionalVariable lang)  where
        satisfies _ = eval

instance Modelable m quant => Modelable m (Quantifiers quant lang) where
    satisfies m (Bind q) = satisfies m q

instance Modelable m abs => Modelable m (Abstractors abs lang) where
    satisfies m (Abstract a) = satisfies m a

instance Modelable m pred => Modelable  m (Predicate pred lang) where
    satisfies m (Predicate p a) = satisfies m p

instance Modelable m con => Modelable m (Connective con lang) where
    satisfies m (Connective p a) = satisfies m p

instance Modelable m func => Modelable m (Function func lang) where
    satisfies m (Function p _) = satisfies m p

instance Modelable m app => Modelable m (Applicators app lang) where
    satisfies m (Apply p) = satisfies m p

instance Modelable m sub => Modelable m (Subnective sub lang) where
    satisfies m (Subnective p a) = satisfies m p

--dummy instance for a type with no constructors
instance Modelable m (EndLang lang) where
        satisfies = undefined

instance (Modelable m (f lang), Modelable m (g lang)) => Modelable m ((f :|: g) lang) where
    satisfies m (FLeft p) = satisfies m p
    satisfies m (FRight p) = satisfies m p

instance (Modelable m (f (Fix f))) => Modelable m (Fix f) where
    satisfies m (Fx a) = satisfies m a

instance (Liftable lang, Modelable m lang) => Modelable m (Copula lang) where
    satisfies m (f :$: x) = satisfies m f (satisfies m x)
    satisfies m (Lam f) = \t -> satisfies m $ f (lift t)
    satisfies m (Lift t) = t

--------------------------------------------------------
--5. First Order Lexicon
--------------------------------------------------------

instance FirstOrderLex (SubstitutionalVariable idx) where

        sameHeadLex (SubVar n) (SubVar m) = n == m

        freshVarsLex = Just $ map SubVar [1 ..]

instance FirstOrderLex quant => FirstOrderLex (Quantifiers quant lang) where
        isVarLex (Bind q) = isVarLex q
        sameHeadLex (Bind q) (Bind q') = sameHeadLex q q'

instance FirstOrderLex app => FirstOrderLex (Applicators app lang) where
        isVarLex (Apply f) = isVarLex f
        sameHeadLex (Apply f) (Apply f') = sameHeadLex f f'
        
instance FirstOrderLex abs => FirstOrderLex (Abstractors abs lang) where
        isVarLex (Abstract a) = isVarLex a
        sameHeadLex (Abstract a) (Abstract b) = sameHeadLex a b

instance FirstOrderLex pred => FirstOrderLex (Predicate pred lang) where
        isVarLex (Predicate p a) = isVarLex p
        sameHeadLex (Predicate p a) (Predicate p' a') =
            show a == show a' && sameHeadLex p p'

instance FirstOrderLex con => FirstOrderLex (Connective con lang) where
        isVarLex (Connective c a) = isVarLex c
        sameHeadLex (Connective c a) (Connective c' a') = 
            show a == show a' && sameHeadLex c c'

instance FirstOrderLex func => FirstOrderLex (Function func lang) where
        isVarLex (Function f a) = isVarLex f
        sameHeadLex (Function f a) (Function f' a') = 
            show a == show a' && sameHeadLex f f'

instance FirstOrderLex sub => FirstOrderLex (Subnective sub lang) where
        isVarLex (Subnective s a) = isVarLex s
        sameHeadLex (Subnective s a) (Subnective s' a') = 
            show a == show a' && sameHeadLex s s'

instance FirstOrderLex (EndLang idx) where
        sameHeadLex = undefined

instance ( FirstOrderLex (f idx)
         , FirstOrderLex (g idx)) => FirstOrderLex ((f :|: g) idx) where
        isVarLex (FLeft a) = isVarLex a
        isVarLex (FRight a) = isVarLex a

        sameHeadLex (FLeft a) (FLeft b) = sameHeadLex a b
        sameHeadLex (FRight a) (FRight b) = sameHeadLex a b
        sameHeadLex _ _ = False

        freshVarsLex = case (freshVarsLex :: Typeable a => Maybe [f idx a], freshVarsLex :: Typeable b => Maybe [g idx b]) of
                           (Just vs, _) -> Just $ map FLeft vs
                           (_, Just vs) -> Just $ map FRight vs
                           _ -> Nothing

instance (UniformlyEq lang, FirstOrderLex lang) => FirstOrderLex (Copula lang)
        where

        sameHeadLex ((x :: lang (t1  -> t2 )) :$: _) 
                    ((y :: lang (t1' -> t2')) :$: _) = 
            case eqT :: Maybe ((t1 -> t2) :~: (t1' -> t2')) of
                Just Refl -> sameHeadLex x y
                Nothing -> False
        sameHeadLex _ _ = False

instance FirstOrderLex (f (Fix f)) => FirstOrderLex (Fix f) where

        isVarLex (Fx x) = isVarLex x

        sameHeadLex (Fx x) (Fx y) = sameHeadLex x y

        freshVarsLex = map Fx <$> freshVarsLex 

instance {-# OVERLAPPABLE #-} (UniformlyEq (FixLang f), FirstOrderLex (FixLang f)) => FirstOrder (FixLang f) where
        
        isVar = isVarLex

        sameHead = sameHeadLex

        decompose a b
            | sameHead a b = recur a b []
            | otherwise = []
            where recur :: FixLang f a -> FixLang f b -> [Equation (FixLang f)]
                    ->[Equation (FixLang f)]
                  recur (x :!$: (y :: FixLang f t)) 
                        (x' :!$: (y' :: FixLang f t')) 
                        terms = case eqT :: Maybe (t :~: t') of
                                    Just Refl -> recur x x' ((y :=: y') : terms) 
                                    Nothing -> []
                  recur _ _ terms = terms

        occurs phi psi@(x :!$: y)= phi =* psi || occurs phi x || occurs phi y
        --might want a clause for LLam
        occurs phi psi = phi =* psi

        subst a@(Fx _ :: FixLang f t) b@(Fx _ :: FixLang f t') c@(Fx _ :: FixLang f t'')
            | a =* b = case eqT :: Maybe (t' :~: t'') of
                           Just Refl -> b
                           Nothing -> c
            | otherwise = case c of
                           (x :!$: y) -> subst a b x :!$: subst a b y
                           --might want a clause for LLam
                           _ -> c
            

        freshVars = case freshVarsLex  of
                        Just fv -> fv
                        Nothing -> error "a store of fresh variables hasn't been included in this language"

--------------------------------------------------------
--Head Extractors and a Generic Plated Instance.
--------------------------------------------------------

(.*$.) :: (Applicative g, Typeable a, Typeable b) => g (FixLang f (a -> b)) -> g (FixLang f a) -> g (FixLang f b)
x .*$. y = (:!$:) <$> x <*> y

handleArg1 :: (Applicative g, LangTypes1 f syn1 sem1)
          => Maybe (tt :~: syn1 sem1) -> (FixLang f (syn1 sem1) 
            -> g (FixLang f (syn1 sem1))) -> FixLang f tt -> g (FixLang f tt)
handleArg1 (Just Refl) f l = f l
handleArg1 Nothing     _ l = pure l

handleArg2 :: (Applicative g, LangTypes2 f syn1 sem1 syn2 sem2)
          => (Maybe (tt :~: syn1 sem1), Maybe (tt :~: syn2 sem2))
          -> (FixLang f (syn1 sem1) -> g (FixLang f (syn1 sem1)))
          -> FixLang f tt
          -> g (FixLang f tt)
handleArg2 (Just Refl, _) f l = f l
handleArg2 (_, Just Refl) f l = difChildren2 f l
handleArg2 (_, _)         _ l = pure l

class (Typeable syn1, Typeable sem1, Typeable syn2, Typeable sem2, BoundVars f) => LangTypes2 f syn1 sem1 syn2 sem2 | f syn1 sem1 -> syn2 sem2 where

        simChildren2 :: Traversal' (FixLang f (syn1 sem1)) (FixLang f (syn1 sem1))
        simChildren2 g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case ( eqT :: Maybe (t' :~: syn1 sem1)
                        , eqT :: Maybe (t' :~: syn2 sem2)) of
                            (Just Refl, _) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBindHeight q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h bv)
                            (_ , Just Refl) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBindHeight q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (difChildren2 g $ h bv)
                            _ -> pure phi
        simChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22, r31, r32) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2) .*$. (handleArg2 (r31, r32) g t3)
        simChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2)
        simChildren2 g phi@(h :!$: (t1 :: FixLang f tt))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                ) of (r11, r12) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1)
        simChildren2 g phi = pure phi

        difChildren2 :: Traversal' (FixLang f (syn2 sem2)) (FixLang f (syn1 sem1))
        difChildren2 g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case ( eqT :: Maybe (t' :~: syn1 sem1)
                        , eqT :: Maybe (t' :~: syn2 sem2)) of
                            (Just Refl, _) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBindHeight q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)
                            (_ , Just Refl) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBindHeight q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (difChildren2 g $ h $ bv)
                            _ -> pure phi
        difChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22, r31, r32) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2) .*$. (handleArg2 (r31, r32) g t3)
        difChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2)
        difChildren2 g phi@(h :!$: (t1 :: FixLang f tt))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                ) of (r11, r12) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1)
        difChildren2 g phi = pure phi

class (Typeable syn1, Typeable sem1, BoundVars f) => LangTypes1 f syn1 sem1 where

        simChildren1 :: Traversal' (FixLang f (syn1 sem1)) (FixLang f (syn1 sem1))
        simChildren1 g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case eqT :: Maybe (t' :~: syn1 sem1) of
                            Just Refl -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBindHeight q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)
                            _ -> pure phi
        simChildren1 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                ) of (r1,  r2,  r3) ->
                                         pure h .*$. (handleArg1 r1 g t1) .*$. (handleArg1 r2 g t2) .*$. (handleArg1 r3 g t3)
        simChildren1 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                ) of (r1, r2) ->
                                         pure h .*$. (handleArg1 r1 g t1) .*$. (handleArg1 r2 g t2)
        simChildren1 g phi@(h :!$: (t1 :: FixLang f tt))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                ) of r1 -> pure h .*$. (handleArg1 r1 g t1)
        simChildren1 g phi = pure phi

instance {-# OVERLAPPABLE #-} LangTypes2 f syn1 sem1 syn2 sem2 => LangTypes1 f syn1 sem1 where
        simChildren1 = simChildren2

instance LangTypes1 f syn sem  => Plated (FixLang f (syn sem)) where
        plate = simChildren1

class (Plated (FixLang f (syn sem)), BoundVars f) => RelabelVars f syn sem where

    relabelVars :: [String] -> FixLang f (syn sem) -> FixLang f (syn sem)
    relabelVars vs phi = S.evalState (transformM trans phi) vs
        where trans :: FixLang f (syn sem) -> S.State [String] (FixLang f (syn sem))
              trans x = do l <- S.get
                           case l of
                             (label:labels) ->
                               case subBinder x label of
                                Just relabeled -> do S.put labels
                                                     return relabeled
                                Nothing -> return x
                             _ -> return x

    subBinder :: FixLang f (syn sem) -> String -> Maybe (FixLang f (syn sem))

    --XXX: could be changed to [[String]], with subBinder also returning an
    --index, in order to accomodate simultaneous relabelings of several types of variables
