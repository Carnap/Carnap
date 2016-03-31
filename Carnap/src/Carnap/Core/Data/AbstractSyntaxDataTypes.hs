{-#LANGUAGE TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, ScopedTypeVariables, AutoDeriveTypeable #-}

module Carnap.Core.Data.AbstractSyntaxDataTypes(
  Modelable, Evaluable, Term(Term), Form(Form), CopulaSchema,
  satisfies, eval, schematize, lift, lift1, lift2, canonical,
  appSchema, lamSchema, liftSchema, BoundVars(..),
  Copula((:$:), Lam), (:|:)(FLeft, FRight), Quantifiers(Bind),Abstractors(Abstract),Applicators(Apply),
  Nat(Zero, Succ), Fix(Fx), Vec(VNil, VCons), Arity(AZero, ASucc),
  TArity(TZero, TSucc),
  Predicate(Predicate), Connective(Connective), Function(Function),
  Subnective(Subnective),CanonicalForm, Schematizable, FixLang, LangTypes, RelabelVars(..),
  pattern AOne, pattern ATwo , pattern LLam, pattern (:!$:),
  pattern Fx1, pattern Fx2, pattern Fx3, pattern Fx4, pattern Fx5, pattern
  Fx6, pattern Fx7, pattern Fx8, pattern Fx9, pattern Fx10, pattern Fx11, EndLang
) where

import Carnap.Core.Util
import Data.Typeable
import Control.Lens
import qualified Control.Monad.State.Lazy as S

--This module attempts to provide abstract syntax types that would cover
--a wide variety of languages


--1. Abstract typeclasses
--------------------------------------------------------

--class of terms that we can compute a fregean denotation for, relative to
--a model or assignment of some sort.
-- | a type is modelable if it can be modeled. these are generally parts from
-- | which LModelable types are built up
class Modelable m f where
    satisfies :: m -> f a -> a

-- | Just like modelable but where a default model is picked for us
-- | this is useful as a convience and when there is one cononical model
-- | such as in the case of peano arithmetic
class Evaluable f where
    eval :: f a -> a

class Liftable f where
    lift :: a -> f a

class Schematizable f where
    schematize :: f a -> [String] -> String

class CopulaSchema lang where
    appSchema :: lang (t -> t') -> lang t -> [String] -> String
    liftSchema :: Copula lang t -> [String] -> String
    lamSchema :: (lang t -> lang t') -> [String] -> String

class CanonicalForm a where
    canonical :: a -> a

lift1 :: (Evaluable f, Liftable f) => (a -> b) -> (f a -> f b)
lift1 f = lift . f . eval

lift2 :: (Evaluable f, Liftable f) => (a -> b -> c) -> (f a -> f b -> f c)
lift2 f fa fb = lift (f (eval fa) (eval fb))

--------------------------------------------------------
--2. Abstract Types
--------------------------------------------------------

--Here are some types for abstract syntax. The basic proposal
--is that we only define how terms of different types connect
--and let the user define all the connections independently of
--of their subparts. In some sense they just define the type
--and the type system figures out how they can go together

--We use the idea of a semantic value to indicate approximately a Fregean
--sense, or intension: approximately a function from models to Fregean
--denotations in those models

--------------------------------------------------------
--2.1 Abstract Terms
--------------------------------------------------------

-- | this is the type that describes how things are connected
-- | Things are connected either by application or by
-- | a lambda abstraction. The 'lang' parameter gets fixed to
-- | form a fully usable type
--
-- @
--    Fix (Copula :|: Copula :|: (Predicate BasicProp :|: Connective BasicConn))
-- @
data Copula lang t where
    (:$:) :: (Typeable t, Typeable t') => lang (t -> t') -> lang t -> Copula lang t'
    Lam :: (Typeable t, Typeable t') => (lang t -> lang t') -> Copula lang (t -> t')
    Lift :: t -> Copula lang t

-- | this is type acts a disjoint sum/union of two functors
-- | it carries though the phantom type as well
data (:|:) :: (k -> k' -> *) -> (k -> k' -> *) -> k -> k' -> * where
    FLeft :: f x idx -> (f :|: g) x idx
    FRight :: g x idx -> (f :|: g) x idx

infixr 5 :|:

-- | This type fixes the first argument of a functor and carries though a
-- | phantom type. note that only certian kinds of functors even have a kind
-- | such that the first argument is fixable
newtype Fix f idx = Fx (f (Fix f) idx)

-- | This is an empty abstract type, which can be used to close off
-- | a series of applications of `:|:`, so that the right-most leaf
-- | doesn't need special treatment.
data EndLang :: (* -> *) -> * -> *

type FixLang f = Fix (Copula :|: f)


pattern (:!$:) f x = Fx (FLeft (f :$: x))
pattern LLam f = Fx (FLeft (Lam f))
pattern Fx1 x  = Fx (FRight (FLeft x))
pattern Fx2 x  = Fx (FRight (FRight (FLeft x)))
pattern Fx3 x  = Fx (FRight (FRight (FRight (FLeft x))))
pattern Fx4 x  = Fx (FRight (FRight (FRight (FRight (FLeft x)))))
pattern Fx5 x  = Fx (FRight (FRight (FRight (FRight (FRight (FLeft x))))))
pattern Fx6 x  = Fx (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x)))))))
pattern Fx7 x  = Fx (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x))))))))
pattern Fx8 x  = Fx (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x)))))))))
pattern Fx9 x  = Fx (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x))))))))))
pattern Fx10 x = Fx (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x)))))))))))
pattern Fx11 x = Fx (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x))))))))))))
pattern Fx12 x = Fx (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FRight (FLeft x)))))))))))))

--XXX: Idea for a uniform definition of plate: the big difficulty here is
--doing a kind very flexible pattern matching, which depends on whether the
--head is Fx_n wrapped around a predicate, a connective, a quantifier, or
--god-knows-what. If we pattern-match, we get type refinements on the RHS,
--which let us put things back together. The best idea right now is to try
--to use a prism, which, given a formula, previews a tuple of the MC and the
--parts if there is an MC, and otherwise nothing. so, something like
--`Prism' (Lang .. (Form a)) (Lang .. (Form b), Lang .. (Form c), Lang .. (Form b -> Form c -> Form a)`.
--We could then reconstruct from parts, or try something new if we get
--nothing. Might be able to build these uniformly using arities. No loss,
--since our connectives have to have uniformly typed arguments anyway.
--
--So, while prisms like this would be nice to have, this just pushes the
--problem back to producing the appropriate prism. Current best idea:
--a typeclass that returns a "Maybe .. (a -> a -> b)" of the appropriate kind, and
--which can be used to drill down into the  :|: structures. Again, maybe
--this can be done uniformly with an arity
data Quantifiers :: (* -> *) -> (* -> *) -> * -> * where
    Bind :: quant ((t a -> f b) -> f b) -> Quantifiers quant lang ((t a -> f b) -> f b)

class BoundVars g where
        getBoundVar :: FixLang g ((a -> b) -> c) -> FixLang g a
        subBoundVar :: FixLang g a -> FixLang g a -> FixLang g b -> FixLang g b


data Abstractors :: (* -> *) -> (* -> *) -> * -> * where
    Abstract :: abs ((t a -> t b) -> t (a -> b)) -> Abstractors abs lang ((t a -> t b) -> t (a -> b))

data Applicators :: (* -> *) -> (* -> *) -> * -> * where
    Apply :: app (t (a -> b) -> t a -> t b) -> Applicators app lang (t (a -> b) -> t a -> t b)

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

-- | think of this as a type constraint. the lang type, model type, and number
-- | must all match up for this type to be inhabited
-- | this lets us do neat type safty things
data Arity :: * -> * -> Nat -> * -> * where
    AZero :: Arity arg ret Zero ret
    ASucc :: Arity arg ret n ret' -> Arity arg ret (Succ n) (arg -> ret')

data TArity :: * -> * -> Nat -> * -> * where
    TZero :: Typeable ret => TArity arg ret Zero ret
    TSucc :: (Typeable ret, Typeable arg, Typeable ret') => TArity arg ret n ret' -> TArity arg ret (Succ n) (arg -> ret')

pattern AOne = (ASucc AZero)
pattern ATwo = (ASucc (ASucc AZero))

data Predicate :: (* -> *) -> (* -> *) -> * -> * where
    Predicate :: pred t -> Arity (Term a) (Form b) n t -> Predicate pred lang t

data Connective :: (* -> *) -> (* -> *) -> * -> * where
    Connective :: con t -> Arity (Form a) (Form b) n t -> Connective con lang t

data Function :: (* -> *) -> (* -> *) -> * -> * where
    Function :: func t -> Arity (Term a) (Term b) n t -> Function func lang t

data Subnective :: (* -> *) -> (* -> *) -> * -> * where
    Subnective :: sub t -> Arity (Form a) (Term b) n t -> Subnective sub lang t

--data Quote :: (* -> *) -> * -> *
    --Quote :: (lang )
--------------------------------------------------------
--3. Schematizable, Show, and Eq
--------------------------------------------------------

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
--Head Extractors and a Generic Plated Instance.
--------------------------------------------------------
class Searchable f l where
        castArity :: (Typeable idx) => TArity a b n t -> f l idx -> Maybe (f l t)
        castArity _ _ = Nothing

instance Searchable (Predicate pred) lang where
        castArity  (TZero :: TArity a b n t) f@(Predicate p (a2 :: Arity (Term a1) (Form b1) n1 idx)) =
            case eqT :: Maybe (t :~: idx) of
                Just Refl -> Just f
                Nothing -> Nothing
        castArity  ((TSucc TZero) :: TArity a b n t) f@(Predicate p (a2 :: Arity (Term a1) (Form b1) n1 idx)) =
            case eqT :: Maybe (t :~: idx) of
                Just Refl -> Just f
                Nothing -> Nothing
        castArity  ((TSucc(TSucc TZero)) :: TArity a b n t) f@(Predicate p (a2 :: Arity (Term a1) (Form b1) n1 idx)) =
            case eqT :: Maybe (t :~: idx) of
                Just Refl -> Just f
                Nothing -> Nothing
        castArity _ _ = Nothing

instance Searchable (Connective con) lang where
        castArity (TZero :: TArity a b n t) f@(Connective c (a2 :: Arity (Form a1) (Form b1) n1 idx)) =
            case eqT :: Maybe (t :~: idx) of
                Just Refl -> Just f
                Nothing -> Nothing
        castArity ((TSucc TZero) :: TArity a b n t) f@(Connective c (a2 :: Arity (Form a1) (Form b1) n1 idx)) =
            case eqT :: Maybe (t :~: idx) of
                Just Refl -> Just f
                Nothing -> Nothing
        castArity ((TSucc (TSucc TZero)) :: TArity a b n t) f@(Connective c (a2 :: Arity (Form a1) (Form b1) n1 idx)) =
            case eqT :: Maybe (t :~: idx) of
                Just Refl -> Just f
                Nothing -> Nothing
        castArity _ _ = Nothing

instance Searchable (Function con) lang

instance Searchable (Subnective sub) lang

instance Searchable (Quantifiers quant) lang

instance Searchable (Abstractors abs) lang

instance Searchable (Applicators app) lang

instance Searchable EndLang lang

instance Searchable Copula lang

instance (Searchable f l, Searchable g l ) =>
        Searchable (f :|: g) l where
        castArity     ar (FLeft a)  = FLeft  <$> castArity ar a
        castArity     ar (FRight a) = FRight <$> castArity ar a

getHead :: (Typeable idx1, Searchable f (Fix f)) => TArity a b n idx -> Fix f idx1 -> Maybe (Fix f idx)
getHead ar (Fx c) = Fx <$> castArity ar c
--TODO: type-safe specializations of this

(.*$.) :: (Applicative g, Typeable a, Typeable b) => g (FixLang f (a -> b)) -> g (FixLang f a) -> g (FixLang f b)
x .*$. y = (:!$:) <$> x <*> y

handleArg :: (Applicative g, LangTypes f syn1 sem1 syn2 sem2)
          => (Maybe (tt :~: syn1 sem1), Maybe (tt :~: syn2 sem2))
          -> (FixLang f (syn1 sem1) -> g (FixLang f (syn1 sem1)))
          -> FixLang f tt
          -> g (FixLang f tt)
handleArg (Just Refl, _) f l = f l
handleArg (_, Just Refl) f l = difChildren f l
handleArg (_, _)         _ l = pure l

class (Typeable syn1, Typeable sem1, Typeable syn2, Typeable sem2, BoundVars f) => LangTypes f syn1 sem1 syn2 sem2 | f syn1 sem1 -> syn2 sem2 where

        simChildren :: Traversal' (FixLang f (syn1 sem1)) (FixLang f (syn1 sem1))
        simChildren g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case ( eqT :: Maybe (t' :~: syn1 sem1)
                        , eqT :: Maybe (t' :~: syn2 sem2)) of
                            (Just Refl, _) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBoundVar q
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)
                            (_ , Just Refl) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBoundVar q
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (difChildren g $ h $ bv)
                            _ -> pure phi
        simChildren g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22, r31, r32) ->
                                         pure h .*$. (handleArg (r11, r12) g t1) .*$. (handleArg (r21, r22) g t2) .*$. (handleArg (r31, r32) g t3)
        simChildren g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22) ->
                                         pure h .*$. (handleArg (r11, r12) g t1) .*$. (handleArg (r21, r22) g t2)
        simChildren g phi@(h :!$: (t1 :: FixLang f tt))= 
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                ) of (r11, r12) ->
                                         pure h .*$. (handleArg (r11, r12) g t1)
        simChildren g phi = pure phi

        difChildren :: Traversal' (FixLang f (syn2 sem2)) (FixLang f (syn1 sem1))
        difChildren g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case ( eqT :: Maybe (t' :~: syn1 sem1)
                        , eqT :: Maybe (t' :~: syn2 sem2)) of
                            (Just Refl, _) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBoundVar q
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)
                            (_ , Just Refl) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = getBoundVar q
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (difChildren g $ h $ bv)
                            _ -> pure phi
        difChildren g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22, r31, r32) ->
                                         pure h .*$. (handleArg (r11, r12) g t1) .*$. (handleArg (r21, r22) g t2) .*$. (handleArg (r31, r32) g t3)
        difChildren g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22) ->
                                         pure h .*$. (handleArg (r11, r12) g t1) .*$. (handleArg (r21, r22) g t2)
        difChildren g phi@(h :!$: (t1 :: FixLang f tt))= 
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                ) of (r11, r12) ->
                                         pure h .*$. (handleArg (r11, r12) g t1)
        difChildren g phi = pure phi

instance LangTypes f syn1 sem1 syn2 sem2 => Plated (FixLang f (syn1 sem1)) where
        plate = simChildren

class (Plated (FixLang f (syn sem)), BoundVars f) => RelabelVars f syn sem where 

    relabelVars :: [String] -> FixLang f (syn sem) -> FixLang f (syn sem)
    relabelVars vs phi = S.evalState (transformM trans phi) vs
        where trans :: FixLang f (syn sem) -> S.State [String] (FixLang f (syn sem))
              trans x = do (label:labels) <- S.get
                           case subBinder x label of
                            Nothing -> return x
                            Just relabeled -> do S.put labels
                                                 return relabeled

    subBinder :: FixLang f (syn sem) -> String -> Maybe (FixLang f (syn sem))
    
    --XXX: could be changed to [[String]], with subBinder also returning an
    --index, in order to accomodate simultaneous relabelings of several types of variables
