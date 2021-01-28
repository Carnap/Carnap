{-#LANGUAGE ScopedTypeVariables,  UndecidableInstances, ConstraintKinds, FlexibleContexts, FlexibleInstances,  GADTs,  PolyKinds, TypeOperators,  PatternSynonyms, MultiParamTypeClasses #-}
module Carnap.Languages.ClassicalSequent.Syntax where

import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Types
import Carnap.Core.Unification.AU
import Carnap.Core.Unification.ACUI
import Carnap.Core.Unification.Unification
import Carnap.Core.Data.Util
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (lens,toListOf,Traversal', Prism', prism')
import Control.Monad.State
import Data.Typeable

--------------------------------------------------------
--1. Sequent Data
--------------------------------------------------------

data Antecedent a = Antecedent a

data Succedent a = Succedent a

data Sequent a = Sequent a

data Cedent :: k -> * -> * where
        NilCedent :: Typeable a => Cedent lang a
        NilAntecedent    :: Typeable a => Cedent lang (Antecedent a )
        -- XXX should be `Cedent lang (Antecedent a)`, but first need a way to make this work with acuiId in the proxy instance
        NilSuccedent     :: Typeable a => Cedent lang (Succedent a)
        SingleAntecedent :: Typeable a => Cedent lang (a -> Antecedent a)
        SingleSuccedent  :: Typeable a => Cedent lang (a -> Succedent a)

instance Schematizable (Cedent a) where
        schematize NilAntecedent xs = "⊤"
        schematize NilSuccedent xs = "⊥"
        schematize NilCedent xs = "∅"
        schematize SingleAntecedent (x:xs) = x
        schematize SingleSuccedent (x:xs) = x 

instance FirstOrderLex (Cedent a)

instance UniformlyEq (Cedent a) where
        NilAntecedent =* NilAntecedent = True
        NilSuccedent =* NilSuccedent = True
        NilCedent =* NilCedent = True
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
pattern SID                 = FX (Lx1 (Lx1 NilCedent))
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

cedentUnfold (x :+: y) = cedentUnfold x ++ cedentUnfold y
cedentUnfold (x :-: y) = cedentUnfold x ++ cedentUnfold y
cedentUnfold Top       = []
cedentUnfold Bot       = []
cedentUnfold SID       = []
cedentUnfold leaf      = [leaf]

cedentId Top = True
cedentId Bot = True
cedentId SID = True
cedentId _   = False


isCedentForm (SS _) = True
isCedentForm (SA _) = True
isCedentForm _ = False

cedentOp a Top = a
cedentOp a Bot = a
cedentOp a SID = a
cedentOp Top b = b
cedentOp Bot b = b
cedentOp SID b = b
cedentOp x@(_ :+: _) y   = x :+: y
cedentOp x y@(_ :+: _)   = x :+: y
cedentOp x@(_ :-: _) y   = x :-: y
cedentOp x y@(_ :-: _)   = x :-: y
cedentOp x@(SA _) y = x :+: y
cedentOp x y@(SA _) = x :+: y
cedentOp x@(SS _) y = x :-: y
cedentOp x y@(SS _) = x :-: y
cedentOp x@(GammaV _) y  = x :+: y
cedentOp x y@(GammaV _)  = x :+: y
cedentOp x@(DeltaV _) y  = x :-: y
cedentOp x y@(DeltaV _)  = x :-: y

instance ( FirstOrderLex (t (ClassicalSequentOver t))
         , StaticVar (ClassicalSequentOver t)
         ) => AU (ClassicalSequentOver t) where

        auUnfold  = cedentUnfold

        isIdAU = cedentId

        isAU  = not . isCedentForm 

        auId p = SID

        auOp = cedentOp

instance ( FirstOrderLex (t (ClassicalSequentOver t))
         , StaticVar (ClassicalSequentOver t)
         ) => ACUI (ClassicalSequentOver t) where

        acuiUnfold = cedentUnfold

        isIdACUI = cedentId

        isACUI  = not . isCedentForm

        acuiId p = SID

        acuiOp = cedentOp

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

instance Typeable a => Concretes lex a

underlyingLex :: Sequentable lex => Prism' (ClassicalSequentOver lex a) (FixLang lex a)
underlyingLex = sublang

instance (Sequentable lex, PrismBooleanConnLex lex b) => PrismBooleanConnLex (ClassicalSequentLexOver lex) b where
        unarylink_PrismBooleanConnLex = underlyingLex . unarylink_PrismBooleanConnLex . relexIso
        binarylink_PrismBooleanConnLex = underlyingLex . binarylink_PrismBooleanConnLex . relexIso
instance (Sequentable lex, PrismGenericContext lex b b) => PrismGenericContext (ClassicalSequentLexOver lex) b b where
        link_GenericContext = underlyingLex . link_GenericContext . relexIso
instance (Sequentable lex, PrismQuantContext lex b c) => PrismQuantContext (ClassicalSequentLexOver lex) b c where
        link_PrismQuantContext = underlyingLex . link_PrismQuantContext . relexIso
instance (Sequentable lex, PrismBooleanConst lex b) => PrismBooleanConst (ClassicalSequentLexOver lex) b where
        link_BooleanConst = underlyingLex . link_BooleanConst . relexIso
instance (Sequentable lex, PrismPropLex lex b) => PrismPropLex (ClassicalSequentLexOver lex) b where
        link_PrismPropLex = underlyingLex . link_PrismPropLex . relexIso
instance (Sequentable lex, PrismSchematicProp lex b) => PrismSchematicProp (ClassicalSequentLexOver lex) b where
        link_PrismSchematicProp = underlyingLex . link_PrismSchematicProp . relexIso
instance (Sequentable lex, PrismGenericQuant lex Term Form b c) => PrismGenericQuant (ClassicalSequentLexOver lex) Term Form b c where
        link_standardQuant = underlyingLex . link_standardQuant .relexIso
instance (Sequentable lex, PrismModality lex b) => PrismModality (ClassicalSequentLexOver lex) b where
        link_PrismModality = underlyingLex . link_PrismModality . relexIso
instance (Sequentable lex, PrismIndexing lex a b c) => PrismIndexing (ClassicalSequentLexOver lex) a b c where
        link_indexer = underlyingLex . link_indexer . relexIso
instance (Sequentable lex, PrismIndexedConstant lex b) => PrismIndexedConstant (ClassicalSequentLexOver lex) b where
        link_IndexedConstant = underlyingLex . link_IndexedConstant . relexIso
instance (Sequentable lex, PrismIntIndex lex b) => PrismIntIndex (ClassicalSequentLexOver lex) b where
        link_IntIndex = underlyingLex . link_IntIndex . relexIso
instance (Sequentable lex, PrismCons lex b) => PrismCons (ClassicalSequentLexOver lex) b where
        link_cons = underlyingLex . link_cons . relexIso
instance (Sequentable lex, PrismPolyadicSchematicFunction lex a b) => PrismPolyadicSchematicFunction (ClassicalSequentLexOver lex) a b where
        link_PrismPolyadicSchematicFunction = underlyingLex . link_PrismPolyadicSchematicFunction . relexIso
instance (Sequentable lex, PrismPolyadicPredicate lex a b) => PrismPolyadicPredicate (ClassicalSequentLexOver lex) a b where
        link_PrismPolyadicPredicate = underlyingLex . link_PrismPolyadicPredicate . relexIso
instance (Sequentable lex, PrismPolyadicSchematicPredicate lex a b) => PrismPolyadicSchematicPredicate (ClassicalSequentLexOver lex) a b where
        link_PrismPolyadicSchematicPredicate = underlyingLex . link_PrismPolyadicSchematicPredicate . relexIso
instance (Sequentable lex, PrismPolyVar lex a b) => PrismPolyVar (ClassicalSequentLexOver lex) a b where
        link_PrismPolyVar = underlyingLex . link_PrismPolyVar . relexIso
instance (Sequentable lex, PrismTermEquality lex a b) => PrismTermEquality (ClassicalSequentLexOver lex) a b where
        link_TermEquality = underlyingLex . link_TermEquality . relexIso
instance (Sequentable lex, PrismTermElements lex a b) => PrismTermElements (ClassicalSequentLexOver lex) a b where
        link_TermElement = underlyingLex . link_TermElement . relexIso
instance (Sequentable lex, PrismElementarySetsLex lex b) => PrismElementarySetsLex (ClassicalSequentLexOver lex) b where
        unarylink_ElementarySetsLex = underlyingLex . unarylink_ElementarySetsLex . relexIso
        binarylink_ElementarySetsLex = underlyingLex . binarylink_ElementarySetsLex . relexIso
instance (Sequentable lex, PrismTermSubset lex c b) => PrismTermSubset (ClassicalSequentLexOver lex) c b where
        link_TermSubset = underlyingLex . link_TermSubset . relexIso
instance (Sequentable lex, PrismSeparating lex b c) => PrismSeparating (ClassicalSequentLexOver lex) b c where
        link_separator = underlyingLex . link_separator . relexIso
instance (Sequentable lex, PrismStandardVar lex b) => PrismStandardVar (ClassicalSequentLexOver lex) b where
        link_StandardVar = underlyingLex . link_StandardVar . relexIso
instance (Sequentable lex, PrismSubstitutionalVariable lex) => PrismSubstitutionalVariable (ClassicalSequentLexOver lex) where
        link_PrismSubstitutionalVar = underlyingLex . link_PrismSubstitutionalVar . relexIso
instance (Sequentable lex, PrismDefiniteDesc lex b c) => PrismDefiniteDesc (ClassicalSequentLexOver lex) b c where
        link_definDesc = underlyingLex . link_definDesc . relexIso

--------------------------------------------------------
--3. Sequent Languages
--------------------------------------------------------

-- XXX : using constraint kinds, we can create  conjunctive typeclass as
-- a tuple.
type Sequentable f = ( PrismLink (EndLang (ClassicalSequentOver f)) (f (ClassicalSequentOver f))
                     , PrismLink (f (ClassicalSequentOver f)) (f (ClassicalSequentOver f))
                     , PrismLink (ClassicalSequentLex (ClassicalSequentOver f)) (f (ClassicalSequentOver f))
                     , PrismLink (ClassicalSequentLexOver f (ClassicalSequentOver f)) (f (ClassicalSequentOver f))
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
