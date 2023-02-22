{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Languages.PureSecondOrder.Syntax
where

import Carnap.Core.Util 
import Carnap.Languages.PureFirstOrder.Syntax (foVar)
import qualified Carnap.Languages.PureFirstOrder.Syntax as FOL
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util (scopeHeight, castTo)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConstructors
import Data.List (intercalate)
import Control.Lens (preview,Prism')

--------------------------------------------------------
--  1. Data for Second Order Logic                    --
--------------------------------------------------------

------------------------
--  1.0 Generic Data  --
------------------------

data SOApplicator a where
        SOApp :: Typeable b => SOApplicator (Form (Int -> b) -> Term Int -> Form b)

instance Schematizable SOApplicator where
        schematize SOApp  = \(x:y:_) -> if last x == ')' then init x ++ "," ++ y  ++ ")"
                                                         else x ++ "(" ++ y ++ ")"

instance UniformlyEq SOApplicator where
    SOApp =* SOApp = True

instance FirstOrderLex SOApplicator

------------------------
--  1.1 Monadic Data  --
------------------------

data MonadicSOVar a where
        MonVar :: String -> MonadicSOVar (Form (Int -> Bool))

instance Schematizable MonadicSOVar where
        schematize (MonVar s) = const s

instance UniformlyEq MonadicSOVar where
    (MonVar n) =* (MonVar m) = n == m

instance FirstOrderLex MonadicSOVar

data MonadicSOScheme a where
        MonScheme :: Int -> MonadicSOScheme (Form (Int -> Bool))

instance Schematizable MonadicSOScheme where
        schematize (MonScheme n) = const $ "ζ_" ++ show n

instance UniformlyEq MonadicSOScheme where
    (MonScheme n) =* (MonScheme m) = n == m

instance FirstOrderLex MonadicSOScheme where
        isVarLex _ = True

type MonadicSOCtx = GenericContext (Int -> Bool) Bool

type MonadicSOQuant = GenericQuant Form Form Bool (Int -> Bool)

-------------------------
--  1.2 Polyadic Data  --
-------------------------

type PolySOLVar = PolyVar Int Bool 
        
data PolyadicSOScheme a where
        PolyScheme :: Typeable t => Int -> Arity Int Bool t ->
            PolyadicSOScheme (Form t)

instance Schematizable PolyadicSOScheme where
        schematize (PolyScheme n a) = const $ "ζ_" ++ show n

instance UniformlyEq PolyadicSOScheme where
    (PolyScheme n a) =* (PolyScheme m b) = n == m && show a == show b

instance FirstOrderLex PolyadicSOScheme where
        isVarLex _ = True

data PolyadicSOCtx a where
        PolyCtx :: Typeable t => Int -> Arity Int Bool t ->
            PolyadicSOCtx (Form t -> Form Bool)

instance Schematizable PolyadicSOCtx where
        schematize (PolyCtx n a) = \(x:_) -> "Φ_" ++ show n ++ "(" ++ x ++ ")"

instance UniformlyEq PolyadicSOCtx where
    (PolyCtx n a) =* (PolyCtx m b) = n == m && show a == show b

instance FirstOrderLex PolyadicSOCtx where
        isVarLex _ = True

data PolySOLQuant a where
        SOPAll :: Typeable t => String -> Arity Int Bool t ->
            PolySOLQuant ((Form t -> Form Bool) -> Form Bool)
        SOPSome :: Typeable t => String -> Arity Int Bool t ->
            PolySOLQuant ((Form t -> Form Bool) -> Form Bool)

instance Schematizable PolySOLQuant where
        schematize (SOPAll v a)  = \(x:_) -> "∀" ++ v ++ x 
        schematize (SOPSome v a) = \(x:_) -> "∃" ++ v ++ x 

instance UniformlyEq PolySOLQuant where
        (SOPAll _ a) =* (SOPAll _ a') = show a == show a'
        (SOPSome _ a) =* (SOPSome _ a') = show a == show a'
        _ =* _ = False

instance FirstOrderLex PolySOLQuant

type OpenSOLLex a = FOL.PureLexiconFOL :|: Abstractors SOLambda :|: Applicators SOApplicator :|: a

type OpenSOL a = FixLang (OpenSOLLex a)

instance PrismPropLex (OpenSOLLex a) Bool
instance PrismSchematicProp (OpenSOLLex a) Bool
instance PrismIndexedConstant (OpenSOLLex a) Int
instance PrismPolyadicPredicate (OpenSOLLex a) Int Bool
instance PrismPolyadicFunction (OpenSOLLex a) Int Int
instance PrismPolyadicSchematicFunction (OpenSOLLex a) Int Int
instance PrismTermEquality (OpenSOLLex a) Int Bool
instance PrismBooleanConnLex (OpenSOLLex a) Bool
instance PrismBooleanConst (OpenSOLLex a) Bool
instance PrismGenericTypedLambda (OpenSOLLex a) Term Form Int
instance PrismStandardVar (OpenSOLLex a) Int
instance PrismSubstitutionalVariable (OpenSOLLex a)
instance PrismGenericQuant (OpenSOLLex a) Term Form Bool Int
instance UniformlyEq (OpenSOL a) => Eq (OpenSOL a b) where
        (==) = (=*)

--------------------------------------------------------
--2. Second Order Languages
--------------------------------------------------------

pattern SOTau c a       = FX (Lx1 (Lx1 (Lx5 (Function c a))))
pattern SOT n           = SOTau (SFunc AZero n) AZero
pattern SOQuant q       = FX (Lx1 (Lx1 (Lx2 (Bind q))))
pattern SOVar c a       = FX (Lx1 (Lx1 (Lx4 (Function c a))))
pattern SOPred x arity  = FX (Lx1 (Lx2 (Lx1 (Predicate x arity))))
pattern SOSPred x arity = FX (Lx1 (Lx2 (Lx2 (Predicate x arity))))
pattern SOFunc x arity  = FX (Lx1 (Lx3 (Lx2 (Function x arity))))
pattern SOP n a1 a2     = SOPred (Pred a1 n) a2
pattern SOPhi n a1 a2   = SOSPred (SPred a1 n) a2
pattern SOV s           = SOVar (Var s) AZero
pattern SOF n a1 a2     = SOFunc (Func a1 n) a2
pattern SOMQuant q      = FX (Lx5 (Bind q))
pattern SOMAbs a        = FX (Lx2 (Abstract a))
pattern SOMApp a        = FX (Lx3 (Apply a))
pattern SOPQuant q      = FX (Lx5 (Bind q))
pattern SOPAbs a        = FX (Lx2 (Abstract a))
pattern SOPApp a        = FX (Lx3 (Apply a))

--------------------------------------------------------
--2.1 Monadic Second Order Logic
--------------------------------------------------------

type MonadicallySOLLex = OpenSOLLex 
                        (Predicate MonadicSOVar
                        :|: Binders MonadicSOQuant
                        :|: Predicate MonadicSOScheme
                        :|: Connective MonadicSOCtx
                        :|: EndLang )

type MonadicallySOL = FixLang MonadicallySOLLex

pattern SOMVar n        = FX (Lx4 (Predicate (MonVar n) AZero))
pattern SOMScheme n     = FX (Lx6 (Predicate (MonScheme n) AZero))
pattern SOMCtx n        = FX (Lx7 (Connective (Context n) AOne))

instance CopulaSchema MonadicallySOL where 

    appSchema (SOQuant (All x)) (LLam f) e = schematize (All x) (show (f $ foVar x) : e)
    appSchema (SOQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ foVar x) : e)
    appSchema (SOMQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SOMVar x) : e)
    appSchema (SOMQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SOMVar x) : e)
    appSchema (SOMAbs (TypedLambda v)) (LLam f) e = schematize (TypedLambda v) (show (f $ foVar v) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance Incrementable MonadicallySOLLex (Term Int) where
    incHead (SOP n a b) = Just $ SOP n (ASucc a) (ASucc a)
    incHead (SOPhi n a b) = Just $ SOPhi n (ASucc a) (ASucc a)
    incHead (SOF n a b) = Just $ SOF n (ASucc a) (ASucc a)
    incHead _  = Nothing

instance BoundVars MonadicallySOLLex where

    scopeUniqueVar (SOQuant (Some v)) (LLam f) = foVar $ show $ scopeHeight (LLam f)
    scopeUniqueVar (SOQuant (All v)) (LLam f)  = foVar $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance PrismGenericQuant MonadicallySOLLex Form Form Bool (Int -> Bool) 

--------------------------------------------------------
--  2.2 Polyadic SOL
--------------------------------------------------------

type PolyadicallySOLLex = OpenSOLLex
                        ( Predicate PolySOLVar
                        :|: Binders PolySOLQuant
                        :|: Predicate PolyadicSOScheme
                        :|: Connective PolyadicSOCtx
                        :|: EndLang)

type PolyadicallySOL = FixLang PolyadicallySOLLex

pattern SOPScheme n a   = FX (Lx6 (Predicate (PolyScheme n a) AZero))
pattern SOPCtx n a      = FX (Lx7 (Connective (PolyCtx n a) AOne))

instance Incrementable PolyadicallySOLLex (Term Int) where
    incHead (SOP n a b)  = Just $ SOP n (ASucc a) (ASucc a)
    incHead (SOPhi n a b) = Just $ SOPhi n (ASucc a) (ASucc a)
    incHead (SOF n a b)  = Just $ SOF n (ASucc a) (ASucc a)
    incHead _  = Nothing

instance BoundVars PolyadicallySOLLex where

    scopeUniqueVar (SOQuant (Some v)) (LLam f)       = foVar $ show $ scopeHeight (LLam f)
    scopeUniqueVar (SOQuant (All v)) (LLam f)        = foVar $ show $ scopeHeight (LLam f)
    scopeUniqueVar (SOPQuant (SOPAll v a)) (LLam f)  = polyVar (show $ scopeHeight (LLam f)) a
    scopeUniqueVar (SOPQuant (SOPSome v a)) (LLam f) = polyVar (show $ scopeHeight (LLam f)) a
    scopeUniqueVar (SOPAbs (TypedLambda v)) (LLam f) = foVar $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance CopulaSchema PolyadicallySOL where 

    appSchema (SOQuant (All x)) (LLam f) e = schematize (All x) (show (f $ foVar x) : e)
    appSchema (SOQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ foVar x) : e)
    appSchema (SOPQuant (SOPAll x a)) (LLam f) e = schematize (SOPAll x a) (show (f $ polyVar x a) : e)
    appSchema (SOPQuant (SOPSome x a)) (LLam f) e = schematize (SOPSome x a) (show (f $ polyVar x a) : e)
    appSchema (SOPAbs (TypedLambda v)) (LLam f) e = schematize (TypedLambda v) (show (f $ foVar v) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance PrismPolyVar PolyadicallySOLLex Int Bool 
--------------------------------------------------------
--Notes
--------------------------------------------------------
--
--Needs to preserve the number of Applications, and the fact that all
--applications are above all Lambdas. The n parameter counts the number of
--applications to drill down through before abstracting.
incLam :: Typeable a => Int -> PolyadicallySOL (Form a) -> PolyadicallySOL (Term Int) 
    -> PolyadicallySOL (Form (Int -> a))
incLam n l@((SOPApp SOApp) :!$: l' :!$: t) v = 
        if n > 0 then (SOPApp SOApp) :!$: (incLam (n - 1) l' v) :!$: t
                 else typedLam (show v) (\x -> subBoundVar v x l)
incLam _ l v = typedLam (show v) (\x -> subBoundVar v x l)

incVar :: Typeable a => PolyadicallySOL (Form a) -> PolyadicallySOL (Form (Int -> a))
incVar ((SOPApp SOApp) :!$: l :!$: t) = (SOPApp SOApp) :!$: (incVar l) :!$: t
incVar v = case preview _polyVarIdxSOL v of
               Just (s,a) -> polyVar s (ASucc a)
               Nothing -> error "attempted to increment the variable of a nonvariable predication"

incScheme :: Typeable a => PolyadicallySOL (Form a) -> PolyadicallySOL (Form (Int -> a))
incScheme ((SOPApp SOApp) :!$: l :!$: t) = (SOPApp SOApp) :!$: (incScheme l) :!$: t
incScheme (SOPScheme s a) = SOPScheme s (ASucc a)
incScheme _ = error "attempted to increment the variable of a nonvariable predication"

incQuant :: PolyadicallySOL (Form Bool) -> PolyadicallySOL (Form Bool)
incQuant ((SOPQuant (SOPAll s a)) :!$: (LLam f)) = 
    (SOPQuant (SOPAll s (ASucc a))) :!$: (LLam $ \x -> subBoundVar (polyVar s (ASucc a)) x (f $ polyVar s a))
incQuant ((SOPQuant (SOPSome s a)) :!$: (LLam f)) = 
    (SOPQuant (SOPSome s (ASucc a))) :!$: (LLam $ \x -> subBoundVar (polyVar s (ASucc a)) x (f $ polyVar s a))
incQuant _ = error "attempted to increment the quantifier of an unquantified sentence"

--increment the context of a higher-order variable
incVarCtx :: PolyadicallySOL (Form Bool) -> PolyadicallySOL (Form Bool)
incVarCtx ((SOPCtx n a) :!$: v) = 
        case preview _polyVarIdxSOL v of
              Just (s, a') -> (SOPCtx n (ASucc a)) :!$: (polyVar s (ASucc a'))
              _ -> error "attempted to increment the variable context of a non-variable/context predicaton"
incVarCtx _ = error "attempted to increment the variable context of a non-variable/context predicaton"

--increment the context of a higher-order schematic variable
incSchemeCtx :: PolyadicallySOL (Form Bool) -> PolyadicallySOL (Form Bool)
incSchemeCtx ((SOPCtx n a) :!$: (SOPScheme s c)) = (SOPCtx n (ASucc a)) :!$: (SOPScheme s (ASucc c))
incSchemeCtx _ = error "attempted to increment the scheme context of a non-scheme/context predicaton"

--Determine whether a formula is a simple predication with a polyadic variable head
psolVarHead :: Typeable a => PolyadicallySOL a -> Bool
psolVarHead ((SOPApp SOApp) :!$: v) = 
        case preview _polyVarIdxSOL v of
               Just _ -> True
               Nothing -> psolVarHead v
psolVarHead (x :!$: _) = psolVarHead x
psolVarHead v = False


--Determine whether a formula is a simple predication with a polyadic variable head
extractPsolVarHead :: (Typeable a) => (forall b . PolyadicallySOL b -> c) -> PolyadicallySOL a -> Maybe c
extractPsolVarHead f ((SOPApp SOApp) :!$: v) = 
        case preview _polyVarIdxSOL v of
               Just _ -> Just $ f v
               Nothing -> extractPsolVarHead f v
extractPsolVarHead f (x :!$: _) = extractPsolVarHead f x
extractPsolVarHead f v = Nothing

msolVarHead :: MonadicallySOL a -> Bool
msolVarHead ((SOMApp SOApp) :!$: x) = msolVarHead x
msolVarHead (x :!$: _) = msolVarHead x
msolVarHead (SOMVar _) = True
msolVarHead _ = False

_polyVarIdxSOL :: Typeable ret => Prism' (PolyadicallySOL (Form ret)) (String, Arity Int Bool ret)
_polyVarIdxSOL = _polyVarIdx

{--
the idea would be for lambda abstraction to work like this:

φ(a) ⊢ (λxφ(x),a)

So interated applications would give, e.g. 

(λy(λxφ(x,y),c), d)

The trouble here is generalizing---there's no subexpression with the type
Form (Int -> Int -> Bool), so it's not clear that where we could introduce a relation variable.

We need an associativity rule, with a schematic variable κ :: Term Int -> Form (Int -> Bool)

(λy(κ(y),c), d) ⊢ ((λyκ(y),d), c)

or more explicitly:

App (λ (LLam $ \y -> App κ(y) c)) d ⊢
App (App (λ (LLam $ \y -> κ(y))) c) d

We can then get a three-place relation via:

φ(a,b,c) ⊢ (λxφ(x,b,c),a)
         ⊢ (λy(λxφ(x,y,c),a),b) 
         ⊢ ((λyλxφ(x,y,c),b),a)             --with κ(y) = λxφ(x,y,c)
         ⊢ (λz((λyλxφ(x,y,z),b),a),c)       
         ⊢ ((λz(λyλxφ(x,y,z),b),c),a)       --with κ(z) = (λyλxφ(x,y,z),b)
         --get stuck here.

basically, what we want is

(λx(λy(λzf(x,y,z),c),b),a) = (((λxλyλzf(x,y,z),a),b),c)

How do you prove this in the lambda calculus? Is substitution required?
It's not obvious what you can do with the RHS other than an internal
β-reduction.

But then we need (sigh) a uniform notion of equality of lambdas, and an
appropriate substitution rule. Both appear to require polymorphic schematic variables. 

What about an internal associativity rule?

Φ(λy(κ(y),c), d) ⊢ Φ((λyκ(y),d), c)

φ(a,b,c) ⊢ (λxφ(x,b,c),a)
         ⊢ (λy(λxφ(x,y,c),a),b) 
         ⊢ ((λyλxφ(x,y,c),b),a)             --with κ(y) = λxφ(x,y,c)
         ⊢ (λz((λyλxφ(x,y,z),b),a),c)       
         ⊢ ((λz(λyλxφ(x,y,z),b),c),a)       --with κ(z) = (λyλxφ(x,y,z),b)
         ⊢ (((λzλyλxφ(x,y,z),c),b),a)       --with κ(z) = λyλxφ(x,y,z)

(still requires polymorphic schematic variable κ)

What about an internal β-abstraction/reduction rule?

φ(a,b,c) ⊢ (λxφ(x,b,c),a)
φ(a,b,c) ⊢ (λx(λyφ(x,y,c),b),a)
φ(a,b,c) ⊢ (λx(λy(λzφ(x,y,z),c),b),a)

Nope. Need a polymorphic rule, roughly

Φ(κ(a)) ⊢ Φ((λyκ(y),a))

where κ can be any lambda term (including a formula). No idea if this will
typecheck, or unify properly, but it does feel like the requirement of
a polymorphic type for lambda terms is unavoidable.

Maybe experiment with a polymorphic beta rule when monadic SOL is up and
running. If it works, it seems like the most elegant option.

--}
