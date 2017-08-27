{-#LANGUAGE ScopedTypeVariables,  UndecidableInstances, ConstraintKinds, FlexibleContexts, FlexibleInstances,  GADTs,  PolyKinds, TypeOperators,  PatternSynonyms, MultiParamTypeClasses #-}
module Carnap.Languages.ClassicalSequent.Syntax where

import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.ACUI
import Carnap.Core.Unification.Unification
import Control.Lens.Lens (lens)
import Control.Lens.Traversal (Traversal')
import Control.Monad.State
import Data.Typeable


--------------------------------------------------------
--1. Sequent Data
--------------------------------------------------------

data Antecedent = Antecedent

data Succedent = Succedent

data Sequent = Sequent

data Cedent :: k -> * -> * where
        NilAntecedent    :: Cedent lang Antecedent
        NilSuccedent     :: Cedent lang Succedent
        SingleAntecedent :: Typeable a => Cedent lang (a -> Antecedent)
        SingleSuccedent  :: Typeable a => Cedent lang (a -> Succedent)

instance Schematizable (Cedent a) where
        schematize NilAntecedent xs = "⊤"
        schematize NilSuccedent xs = "⊥"
        schematize SingleAntecedent (x:xs) = x
        schematize SingleSuccedent (x:xs) = x 

instance FirstOrderLex (Cedent a)

instance Monad m => MaybeMonadVar (Cedent a) m

instance MaybeStaticVar (Cedent a)

instance UniformlyEq (Cedent a) where
        NilAntecedent =* NilAntecedent = True
        NilSuccedent =* NilSuccedent = True
        SingleAntecedent =* SingleAntecedent = True
        SingleSuccedent =* SingleSuccedent = True
        _ =* _ = False

data CedentVar :: k -> * -> * where
        Gamma :: Int -> CedentVar lang Antecedent
        Delta :: Int -> CedentVar lang Succedent

instance UniformlyEq (CedentVar a) where
        Gamma n =* Gamma m = n == m
        Delta n =* Delta m = n == m
        _ =* _ = False

instance Schematizable (CedentVar a) where
        schematize (Gamma n) [] = "Γ_" ++ show n
        schematize (Delta n) [] = "Δ_" ++ show n

instance FirstOrderLex (CedentVar a) where
        isVarLex _ = True

instance Monad m => MaybeMonadVar (CedentVar a) m

instance MaybeStaticVar (CedentVar a)

data Comma :: k -> * -> * where
        AnteComma :: Comma lang (Antecedent -> Antecedent -> Antecedent)
        SuccComma :: Comma lang (Succedent -> Succedent-> Succedent)

instance UniformlyEq (Comma a) where
        AnteComma =* AnteComma = True
        SuccComma =* SuccComma = True
        _ =* _ = False

instance Schematizable (Comma a) where
        schematize AnteComma (x:"⊤":[]) = x
        schematize AnteComma (x:y:[])  = x ++ ", " ++ y
        schematize SuccComma (x:"⊥":[]) = x
        schematize SuccComma (x:y:[])  = x ++ ", " ++ y

instance FirstOrderLex (Comma a)

instance Monad m => MaybeMonadVar (Comma a) m

instance MaybeStaticVar (Comma a)

data Turnstile :: k -> * -> * where
        Turnstile :: Turnstile lang (Antecedent -> Succedent -> Sequent)

instance Schematizable (Turnstile a) where
        schematize Turnstile (x:y:xs) = x ++ " ⊢ " ++ y

instance FirstOrderLex (Turnstile a)

instance UniformlyEq (Turnstile a) where
        Turnstile =* Turnstile = True

instance Monad m => MaybeMonadVar (Turnstile a) m

instance MaybeStaticVar (Turnstile a)

type ClassicalSequentLex = Cedent
                           :|: Comma
                           :|: Turnstile
                           :|: CedentVar
                           :|: EndLang

type ClassicalSequentOver a = FixLang (ClassicalSequentLex :|: a :|: EndLang)

pattern Top                 = FX (Lx1 (Lx1 NilAntecedent))
pattern Bot                 = FX (Lx1 (Lx1 NilSuccedent))
pattern SA x                = FX (Lx1 (Lx1 SingleAntecedent)) :!$: x
pattern SS x                = FX (Lx1 (Lx1 SingleSuccedent)) :!$: x
pattern (:+:) x y           = FX (Lx1 (Lx2 AnteComma)) :!$: x :!$: y
pattern (:-:) x y           = FX (Lx1 (Lx2 SuccComma)) :!$: x :!$: y
pattern (:|-:) x y          = FX (Lx1 (Lx3 Turnstile)) :!$: x :!$: y
pattern GammaV n            = FX (Lx1 (Lx4 (Gamma n)))
pattern DeltaV n            = FX (Lx1 (Lx4 (Delta n)))

-- we set the fixity thus to reduce the need for parentheses when using :+:
infixr 7 :|-:

-- we set the fixity thus to reduce the need for parentheses when using
-- infix formula building operations
infixr 8 :+:

infixr 8 :-:

instance ( MaybeStaticVar (t (ClassicalSequentOver t))
         , FirstOrderLex (t (ClassicalSequentOver t))
         ) => ACUI (ClassicalSequentOver t) where

        unfoldTerm (x :+: y) = unfoldTerm x ++ unfoldTerm y
        unfoldTerm Top       = []
        unfoldTerm leaf      = [leaf]

        isId Top = True
        isId _   = False

        isACUI (SA _)     = False
        isACUI _ = True

        getId (Proxy :: Proxy a) = 
            case eqT :: Maybe (a :~: Antecedent) of
               Just Refl -> Top
               _         -> error "you have to use the right type 1"

        acuiOp a Top = a
        acuiOp Top b = b
        acuiOp x@(_ :+: _) y   = x :+: y
        acuiOp x y@(_ :+: _)   = x :+: y
        acuiOp x@(SA _) y = x :+: y
        acuiOp x y@(SA _) = x :+: y
        acuiOp x@(GammaV _) y  = x :+: y
        acuiOp x y@(GammaV _)  = x :+: y

instance Handed (ClassicalSequentOver lex Sequent) 
                (ClassicalSequentOver lex Antecedent)
                (ClassicalSequentOver lex Succedent)
    where lhs = lens (\(x :|-: y) -> x) (\( y:|-:z ) x -> x:|-: z)
          rhs = lens (\(x :|-: y) -> y) (\( y:|-:z ) x -> y:|-: x)

data SequentRule a = SequentRule { upperSequents :: [ClassicalSequentOver a Sequent]
                                 , lowerSequent :: ClassicalSequentOver a Sequent
                                 }

instance Show (ClassicalSequentOver a Sequent) => Show (SequentRule a) where
        show (SequentRule us ls) = show us ++ " ∴ " ++ show ls

(∴) = SequentRule

infixr 6 ∴

--------------------------------------------------------
--2. Optics
--------------------------------------------------------

class Typeable a => Concretes lex a where
    concretes :: Traversal' (ClassicalSequentOver lex b) (ClassicalSequentOver lex a)
    concretes f (a :|-: a') = (:|-:) <$> concretes f a <*> concretes f a'
    concretes f (a :+: a') = (:+:) <$> concretes f a <*> concretes f a'
    concretes f (a :-: a') = (:-:) <$> concretes f a <*> concretes f a'
    concretes f (SA (x :: ClassicalSequentOver lex b)) = 
        case eqT :: Maybe (a :~: b) of
            Just Refl -> SA <$> f x
            Nothing -> pure (SA x)
    concretes f (SS (x :: ClassicalSequentOver lex b)) = 
        case eqT :: Maybe (a :~: b) of
            Just Refl -> SS <$> f x
            Nothing -> pure (SS x)
    concretes f (GammaV n) = pure (GammaV n)
    concretes f (Top) = pure Top
    concretes f (Bot) = pure Bot

instance Concretes lex (Form Bool)

--------------------------------------------------------
--3. Sequent Languages
--------------------------------------------------------

-- XXX : using constraint kinds, we can create  conjunctive typeclass as
-- a tuple.
type Sequentable f = ( PrismLink (EndLang (ClassicalSequentOver f)) (f (ClassicalSequentOver f))
                     , PrismLink (f (ClassicalSequentOver f)) (f (ClassicalSequentOver f))
                     , PrismLink (ClassicalSequentLex (ClassicalSequentOver f)) (f (ClassicalSequentOver f))
                     , ReLex f, f :<: (ClassicalSequentLex :|: f :|: EndLang))

liftToSequent :: Sequentable f => FixLang f a -> ClassicalSequentOver f a
liftToSequent x = liftLang x

fromSequent :: Sequentable f => ClassicalSequentOver f a -> FixLang f a
fromSequent x = case lowerLang x of
                    Just y -> y
                    Nothing -> error "could not lower sequent"

liftSequent :: (Sequentable f, Sequentable g, f :<: g) => ClassicalSequentOver f a -> ClassicalSequentOver g a
liftSequent Top = Top
liftSequent (GammaV n) = GammaV n
liftSequent (DeltaV n) = DeltaV n
liftSequent (x :+: y) = liftSequent x :+: liftSequent y
liftSequent (x :-: y) = liftSequent x :-: liftSequent y
liftSequent (x :|-: y) = liftSequent x :|-: liftSequent y
liftSequent (SA x) = SA $ liftToSequent (liftLang (fromSequent x) )
liftSequent (SS x) = SS $ liftToSequent (liftLang (fromSequent x) )

--------------------------------------------------------
--4. Utilities
--------------------------------------------------------

antecedentNub :: 
    ( ACUI (ClassicalSequentOver a)
    , MonadVar (ClassicalSequentOver a) (State Int)
    ) => ClassicalSequentOver a Sequent -> ClassicalSequentOver a Sequent
antecedentNub (x:|-:y) = (applySub (head subs) (GammaV 1) :|-: y)
    where subs = evalState (acuiUnifySys (const False) [x :=: GammaV 1]) (0 :: Int)
