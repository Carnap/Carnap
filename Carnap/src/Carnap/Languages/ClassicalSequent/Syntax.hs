{-#LANGUAGE ScopedTypeVariables,  UndecidableInstances, ConstraintKinds, FlexibleContexts, FlexibleInstances,  GADTs,  PolyKinds, TypeOperators,  PatternSynonyms, MultiParamTypeClasses #-}
module Carnap.Languages.ClassicalSequent.Syntax where

import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Types
import Carnap.Core.Unification.ACUI
import Carnap.Core.Unification.Unification
import Carnap.Core.Data.Util
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (lens,toListOf,Traversal')
import Control.Monad.State
import Data.Typeable

--------------------------------------------------------
--1. Sequent Data
--------------------------------------------------------

data Antecedent a = Antecedent a

data Succedent a = Succedent a

data Sequent a = Sequent a

data Cedent :: k -> * -> * where
        NilAntecedent    :: Typeable a => Cedent lang a 
        -- XXX should be `Cedent lang (Antecedent a)`, but first need a way to make this work with getId in the proxy instance
        NilSuccedent     :: Typeable a => Cedent lang (Succedent a)
        SingleAntecedent :: Typeable a => Cedent lang (a -> Antecedent a)
        SingleSuccedent  :: Typeable a => Cedent lang (a -> Succedent a)

instance Schematizable (Cedent a) where
        schematize NilAntecedent xs = "⊤"
        schematize NilSuccedent xs = "⊥"
        schematize SingleAntecedent (x:xs) = x
        schematize SingleSuccedent (x:xs) = x 

instance FirstOrderLex (Cedent a)

instance UniformlyEq (Cedent a) where
        NilAntecedent =* NilAntecedent = True
        NilSuccedent =* NilSuccedent = True
        SingleAntecedent =* SingleAntecedent = True
        SingleSuccedent =* SingleSuccedent = True
        _ =* _ = False

data CedentVar :: k -> * -> * where
        Gamma :: Typeable a => Int -> CedentVar lang (Antecedent a)
        Delta :: Typeable a => Int -> CedentVar lang (Succedent a)

instance UniformlyEq (CedentVar a) where
        Gamma n =* Gamma m = n == m
        Delta n =* Delta m = n == m
        _ =* _ = False

instance Schematizable (CedentVar a) where
        schematize (Gamma n) [] = "Γ_" ++ show n
        schematize (Delta n) [] = "Δ_" ++ show n

instance FirstOrderLex (CedentVar a) where
        isVarLex _ = True

data Comma :: k -> * -> * where
        AnteComma :: Comma lang (Antecedent a -> Antecedent a -> Antecedent a)
        SuccComma :: Comma lang (Succedent a -> Succedent a-> Succedent a)

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

data Turnstile :: k -> * -> * where
        Turnstile :: Turnstile lang (Antecedent a -> Succedent a -> Sequent a)

instance Schematizable (Turnstile a) where
        schematize Turnstile (x:y:xs) = x ++ " ⊢ " ++ y

instance FirstOrderLex (Turnstile a)

instance UniformlyEq (Turnstile a) where
        Turnstile =* Turnstile = True

type ClassicalSequentLex = Cedent
                           :|: Comma
                           :|: Turnstile
                           :|: CedentVar
                           :|: EndLang

type ClassicalSequentLexOver a = ClassicalSequentLex :|: a :|: EndLang

type ClassicalSequentOver a = FixLang (ClassicalSequentLexOver a)

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

instance ( FirstOrderLex (t (ClassicalSequentOver t))
         , StaticVar (ClassicalSequentOver t)
         ) => ACUI (ClassicalSequentOver t) where

        unfoldTerm (x :+: y) = unfoldTerm x ++ unfoldTerm y
        unfoldTerm Top       = []
        unfoldTerm leaf      = [leaf]

        isId Top = True
        isId _   = False

        isACUI (SA _) = False
        isACUI _      = True

        getId _ = Top
            -- case (eqT :: Maybe (a :~: Antecedent b)) of
            --    Just Refl -> Top
            --    _         -> error "you have to use the right type 1"

        acuiOp a Top = a
        acuiOp Top b = b
        acuiOp x@(_ :+: _) y   = x :+: y
        acuiOp x y@(_ :+: _)   = x :+: y
        acuiOp x@(SA _) y = x :+: y
        acuiOp x y@(SA _) = x :+: y
        acuiOp x@(GammaV _) y  = x :+: y
        acuiOp x y@(GammaV _)  = x :+: y

instance Handed (ClassicalSequentOver lex (Sequent a)) 
                (ClassicalSequentOver lex (Antecedent a))
                (ClassicalSequentOver lex (Succedent a))
    where lhs = lens (\(x :|-: y) -> x) (\( y:|-:z ) x -> x:|-: z)
          rhs = lens (\(x :|-: y) -> y) (\( y:|-:z ) x -> y:|-: x)

data SequentRule lex a = SequentRule { upperSequents :: [ClassicalSequentOver lex (Sequent a)]
                                     , lowerSequent :: ClassicalSequentOver lex (Sequent a)
                                     }

instance Show (ClassicalSequentOver lex (Sequent a)) => Show (SequentRule lex a) where
        show (SequentRule us ls) = show us ++ " ∴ " ++ show ls

(∴) = SequentRule

infixr 6 ∴

--------------------------------------------------------
--2. Optics
--------------------------------------------------------

class Typeable a => Concretes lex a where
    concretes :: Typeable b => Traversal' (ClassicalSequentOver lex b) (ClassicalSequentOver lex a)
    concretes f (a :|-: a') = (:|-:) <$> concretes f a <*> concretes f a'
    concretes f (a :+: a') = (:+:) <$> concretes f a <*> concretes f a'
    concretes f (a :-: a') = (:-:) <$> concretes f a <*> concretes f a'
    concretes f (SA x) = SA <$> concretes f x
    concretes f (SS x) = SS <$> concretes f x
    concretes f (GammaV n) = pure (GammaV n)
    concretes f (Top) = pure Top
    concretes f (Bot) = pure Bot
    concretes f (x :: ClassicalSequentOver lex b) = 
        case eqT :: Maybe (a :~: b) of
            Just Refl -> f x
            Nothing -> pure x

instance Concretes lex (Form Bool)

instance PrismBooleanConnLex lex b => PrismBooleanConnLex (ClassicalSequentLexOver lex) b
instance PrismGenericContext lex b b => PrismGenericContext (ClassicalSequentLexOver lex) b b
instance PrismBooleanConst lex b => PrismBooleanConst (ClassicalSequentLexOver lex) b
instance PrismPropLex lex b => PrismPropLex (ClassicalSequentLexOver lex) b
instance PrismSchematicProp lex b => PrismSchematicProp (ClassicalSequentLexOver lex) b
instance PrismGenericQuant lex Term Form b c => PrismGenericQuant (ClassicalSequentLexOver lex) Term Form b c
instance PrismModality lex b => PrismModality (ClassicalSequentLexOver lex) b
instance PrismIndexing lex a b c => PrismIndexing (ClassicalSequentLexOver lex) a b c
instance PrismIndexedConstant lex b => PrismIndexedConstant (ClassicalSequentLexOver lex) b
instance PrismIntIndex lex b => PrismIntIndex (ClassicalSequentLexOver lex) b
instance PrismCons lex b => PrismCons (ClassicalSequentLexOver lex) b
instance PrismPolyadicSchematicFunction lex a b => PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) a b
instance PrismPolyadicSchematicPredicate lex a b => PrismPolyadicSchematicPredicate (ClassicalSequentLexOver lex) a b
instance PrismPolyVar lex a b => PrismPolyVar (ClassicalSequentLexOver lex) a b
instance PrismTermEquality lex a b => PrismTermEquality (ClassicalSequentLexOver lex) a b
instance PrismTermElements lex a b => PrismTermElements (ClassicalSequentLexOver lex) a b
instance PrismElementarySetsLex lex b => PrismElementarySetsLex (ClassicalSequentLexOver lex) b
instance PrismTermSubset lex c b => PrismTermSubset (ClassicalSequentLexOver lex) c b
instance PrismSeparating lex b c => PrismSeparating (ClassicalSequentLexOver lex) b c
instance PrismStandardVar lex b => PrismStandardVar (ClassicalSequentLexOver lex) b
instance PrismSubstitutionalVariable lex => PrismSubstitutionalVariable (ClassicalSequentLexOver lex)

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
    ( Typeable a
    , ACUI (ClassicalSequentOver lex)
    , MonadVar (ClassicalSequentOver lex) (State Int)
    ) => ClassicalSequentOver lex (Sequent a) -> ClassicalSequentOver lex (Sequent a)
antecedentNub (x:|-:y) = (applySub (head subs) (GammaV 1) :|-: y)
    where subs = evalState (acuiUnifySys (const False) [x :=: GammaV 1]) (0 :: Int)

multiCutLeft :: (Typeable a, Concretes lex a) => ClassicalSequentOver lex (Sequent a) -> [ClassicalSequentOver lex (Sequent a)]
multiCutLeft r = zipWith gammafy (toListOf (lhs . concretes) r) [1..]
        where gammafy p n = GammaV n :|-: SS p

multiCutRight :: (Typeable a, Concretes lex a) => ClassicalSequentOver lex (Sequent a) -> ClassicalSequentOver lex (Sequent a)
multiCutRight r = gammas :|-: SS (head . toListOf (rhs . concretes) $ r)
        where gammas = foldl (:+:) Top (map GammaV [1 .. length (multiCutLeft r)])
