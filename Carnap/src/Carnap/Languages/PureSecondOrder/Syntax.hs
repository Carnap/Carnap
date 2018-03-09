{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Languages.PureSecondOrder.Syntax
where

import Carnap.Core.Util 
import qualified Carnap.Languages.PureFirstOrder.Syntax as FOL
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConstructors
import Data.List (intercalate)

--------------------------------------------------------
--  1. Data for Second Order Logic                    --
--------------------------------------------------------

------------------------
--  1.0 Generic Data  --
------------------------

data SOLambda a where
        SOLam :: String -> SOLambda ((Term Int -> Form b) -> Form (Int -> b))

instance UniformlyEq SOLambda where
    (SOLam _) =* (SOLam _) = True

instance Monad m => MaybeMonadVar SOLambda m

instance MaybeStaticVar SOLambda

instance FirstOrderLex SOLambda

instance Schematizable SOLambda where
        schematize (SOLam v)  = \(x:_) -> if last x == ']' then "λ" ++ v ++ x
                                                           else "λ" ++ v ++ "[" ++ x ++ "]"

data SOApplicator a where
        SOApp :: SOApplicator (Form (Int -> b) -> Term Int -> Form b)

instance Schematizable SOApplicator where
        schematize SOApp  = \(x:y:_) -> if last x == ')' then init x ++ "," ++ y  ++ ")"
                                                         else x ++ "(" ++ y ++ ")"

instance UniformlyEq SOApplicator where
    SOApp =* SOApp = True

instance Monad m => MaybeMonadVar SOApplicator m

instance MaybeStaticVar SOApplicator

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

instance Monad m => MaybeMonadVar MonadicSOVar m

instance MaybeStaticVar MonadicSOVar

instance FirstOrderLex MonadicSOVar

data MonadicSOScheme a where
        MonScheme :: Int -> MonadicSOScheme (Form (Int -> Bool))

instance Schematizable MonadicSOScheme where
        schematize (MonScheme n) = const $ "ζ_" ++ show n

instance UniformlyEq MonadicSOScheme where
    (MonScheme n) =* (MonScheme m) = n == m

instance Monad m => MaybeMonadVar MonadicSOScheme m

instance MaybeStaticVar MonadicSOScheme

instance FirstOrderLex MonadicSOScheme where
        isVarLex _ = True

-- XXX this is a good candidate for a generic constructor
data MonadicSOCtx a where
        MonCtx :: Int -> MonadicSOCtx (Form (Int -> Bool) -> Form Bool)

instance Schematizable MonadicSOCtx where
        schematize (MonCtx n) = \(x:_) -> "Φ_" ++ show n ++ "(" ++ x ++ ")"

instance UniformlyEq MonadicSOCtx where
    (MonCtx n) =* (MonCtx m) = n == m

instance Monad m => MaybeMonadVar MonadicSOCtx m

instance MaybeStaticVar MonadicSOCtx

instance FirstOrderLex MonadicSOCtx where
        isVarLex _ = True

data MonadicSOQuant a where
        SOAll :: String -> 
            MonadicSOQuant ((Form (Int -> Bool) -> Form Bool) -> Form Bool)
        SOSome :: String -> 
            MonadicSOQuant ((Form (Int -> Bool) -> Form Bool) -> Form Bool)

instance Schematizable MonadicSOQuant where
        schematize (SOAll v)  = \(x:_) -> "∀" ++ v ++ x 
        schematize (SOSome v) = \(x:_) -> "∃" ++ v ++ x 

instance UniformlyEq MonadicSOQuant where
        (SOAll _) =* (SOAll _) = True
        (SOSome _) =* (SOSome _) = True
        _ =* _ = False

instance Monad m => MaybeMonadVar MonadicSOQuant m

instance MaybeStaticVar MonadicSOQuant

instance FirstOrderLex MonadicSOQuant


-------------------------
--  1.2 Polyadic Data  --
-------------------------

data PolySOLVar a where
        PolyVar :: String -> Arity Int Bool n t -> PolySOLVar (Form t)

instance Schematizable PolySOLVar where
        schematize (PolyVar s a) = const s

instance UniformlyEq PolySOLVar where
    (PolyVar n a) =* (PolyVar m a') = n == m && show a == show a'

instance Monad m => MaybeMonadVar PolySOLVar m 
instance MaybeStaticVar PolySOLVar

instance FirstOrderLex PolySOLVar
        
data PolyadicSOScheme a where
        PolyScheme :: Typeable t => Int -> Arity Int Bool n t ->
            PolyadicSOScheme (Form t)

instance Schematizable PolyadicSOScheme where
        schematize (PolyScheme n a) = const $ "ζ_" ++ show n

instance UniformlyEq PolyadicSOScheme where
    (PolyScheme n a) =* (PolyScheme m b) = n == m && show a == show b

instance Monad m => MaybeMonadVar PolyadicSOScheme m

instance MaybeStaticVar PolyadicSOScheme

instance FirstOrderLex PolyadicSOScheme where
        isVarLex _ = True

data PolyadicSOCtx a where
        PolyCtx :: Typeable t => Int -> Arity Int Bool n t ->
            PolyadicSOCtx (Form t -> Form Bool)

instance Schematizable PolyadicSOCtx where
        schematize (PolyCtx n a) = \(x:_) -> "Φ_" ++ show n ++ "(" ++ x ++ ")"

instance UniformlyEq PolyadicSOCtx where
    (PolyCtx n a) =* (PolyCtx m b) = n == m && show a == show b

instance Monad m => MaybeMonadVar PolyadicSOCtx m

instance MaybeStaticVar PolyadicSOCtx

instance FirstOrderLex PolyadicSOCtx where
        isVarLex _ = True

data PolySOLQuant a where
        SOPAll :: Typeable t => String -> Arity Int Bool n t ->
            PolySOLQuant ((Form t -> Form Bool) -> Form Bool)
        SOPSome :: Typeable t => String -> Arity Int Bool n t ->
            PolySOLQuant ((Form t -> Form Bool) -> Form Bool)

instance Schematizable PolySOLQuant where
        schematize (SOPAll v a)  = \(x:_) -> "∀" ++ v ++ x 
        schematize (SOPSome v a) = \(x:_) -> "∃" ++ v ++ x 

instance UniformlyEq PolySOLQuant where
        (SOPAll _ a) =* (SOPAll _ a') = show a == show a'
        (SOPSome _ a) =* (SOPSome _ a') = show a == show a'
        _ =* _ = False

instance Monad m => MaybeMonadVar PolySOLQuant m

instance MaybeStaticVar PolySOLQuant

instance FirstOrderLex PolySOLQuant

--------------------------------------------------------
--2. Second Order Languages
--------------------------------------------------------

pattern SOSV n          = FX (Lx1 (Lx1 (Lx1 (Lx4 (StaticVar n)))))
pattern SODV n          = FX (Lx1 (Lx1 (Lx1 (Lx4 (SubVar n)))))
pattern SOConst c a     = FX (Lx1 (Lx1 (Lx3 (Function c a))))
pattern SOTau c a       = FX (Lx1 (Lx1 (Lx5 (Function c a))))
pattern SOC n           = SOConst (Constant n) AZero
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
pattern SOMQuant q      = FX (Lx3 (Bind q))
pattern SOMAbs a        = FX (Lx4 (Abstract a))
pattern SOMApp a        = FX (Lx5 (Apply a))
pattern SOAbstract l f  = SOMAbs l :!$: LLam f
pattern SOMBind q f     = SOMQuant q :!$: LLam f
pattern SOPQuant q      = FX (Lx3 (Bind q))
pattern SOPAbs a        = FX (Lx4 (Abstract a))
pattern SOPApp a        = FX (Lx5 (Apply a))
pattern SOPBind q f     = SOPQuant q :!$: LLam f

--------------------------------------------------------
--2.1 Monadic Second Order Logic
--------------------------------------------------------

type MonadicallySOLLex = FOL.PureLexiconFOL
                        :|: Predicate MonadicSOVar
                        :|: Quantifiers MonadicSOQuant
                        :|: Abstractors SOLambda
                        :|: Applicators SOApplicator
                        :|: Predicate MonadicSOScheme
                        :|: Connective MonadicSOCtx
                        :|: EndLang

type MonadicallySOL = FixLang MonadicallySOLLex

pattern SOMVar n        = FX (Lx2 (Predicate (MonVar n) AZero))
pattern SOMScheme n     = FX (Lx6 (Predicate (MonScheme n) AZero))
pattern SOMCtx n        = FX (Lx7 (Connective (MonCtx n) AOne))

instance CopulaSchema MonadicallySOL where 

    appSchema (SOQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SOV x) : e)
    appSchema (SOQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SOV x) : e)
    appSchema (SOMQuant (SOAll x)) (LLam f) e = schematize (SOAll x) (show (f $ SOMVar x) : e)
    appSchema (SOMQuant (SOSome x)) (LLam f) e = schematize (SOSome x) (show (f $ SOMVar x) : e)
    appSchema (SOMAbs (SOLam v)) (LLam f) e = schematize (SOLam v) (show (f $ SOV v) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

instance Incrementable MonadicallySOLLex (Term Int) where
    incHead (SOP n a b) = Just $ SOP n (ASucc a) (ASucc a)
    incHead (SOPhi n a b) = Just $ SOPhi n (ASucc a) (ASucc a)
    incHead (SOF n a b) = Just $ SOF n (ASucc a) (ASucc a)
    incHead _  = Nothing

instance BoundVars MonadicallySOLLex where

    scopeUniqueVar (SOQuant (Some v)) (LLam f) = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar (SOQuant (All v)) (LLam f)  = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance Eq (MonadicallySOL a) where
        (==) = (=*)

instance PrismPropLex MonadicallySOLLex Bool
instance PrismSchematicProp MonadicallySOLLex Bool
instance PrismIndexedConstant MonadicallySOLLex Int
instance PrismPolyadicPredicate MonadicallySOLLex Int Bool
instance PrismPolyadicFunction MonadicallySOLLex Int Int
instance PrismPolyadicSchematicFunction MonadicallySOLLex Int Int
instance PrismTermEquality MonadicallySOLLex Int Bool
instance PrismBooleanConnLex MonadicallySOLLex Bool
instance PrismStandardQuant MonadicallySOLLex Bool Int

instance QuantLanguage (MonadicallySOL (Form Bool)) (MonadicallySOL (Form (Int -> Bool))) where
    lall  v f = SOMQuant (SOAll v) :!$: LLam f
    lsome  v f = SOMQuant (SOSome v) :!$: LLam f

--------------------------------------------------------
--  2.2 Polyadic SOL
--------------------------------------------------------

type PolyadicallySOLLex = FOL.PureLexiconFOL
                        :|: Predicate PolySOLVar
                        :|: Quantifiers PolySOLQuant
                        :|: Abstractors SOLambda
                        :|: Applicators SOApplicator
                        :|: Predicate PolyadicSOScheme
                        :|: Connective PolyadicSOCtx
                        :|: EndLang

type PolyadicallySOL = FixLang PolyadicallySOLLex

pattern SOPVar n a      = FX (Lx2 (Predicate (PolyVar n a) AZero))
pattern SOPScheme n a   = FX (Lx6 (Predicate (PolyScheme n a) AZero))
pattern SOPCtx n a      = FX (Lx7 (Connective (PolyCtx n a) AOne))

instance Incrementable PolyadicallySOLLex (Term Int) where
    incHead (SOP n a b)  = Just $ SOP n (ASucc a) (ASucc a)
    incHead (SOPhi n a b) = Just $ SOPhi n (ASucc a) (ASucc a)
    incHead (SOF n a b)  = Just $ SOF n (ASucc a) (ASucc a)
    incHead _  = Nothing

instance BoundVars PolyadicallySOLLex where

    scopeUniqueVar (SOQuant (Some v)) (LLam f) = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar (SOQuant (All v)) (LLam f)  = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance CopulaSchema PolyadicallySOL where 

    appSchema (SOQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SOV x) : e)
    appSchema (SOQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SOV x) : e)
    appSchema (SOPQuant (SOPAll x a)) (LLam f) e = schematize (SOPAll x a) (show (f $ SOPVar x a) : e)
    appSchema (SOPQuant (SOPSome x a)) (LLam f) e = schematize (SOPSome x a) (show (f $ SOPVar x a) : e)
    appSchema (SOPAbs (SOLam v)) (LLam f) e = schematize (SOLam v) (show (f $ SOV v) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

instance Eq (PolyadicallySOL a) where
        (==) = (=*)

instance PrismPropLex PolyadicallySOLLex Bool
instance PrismSchematicProp PolyadicallySOLLex Bool
instance PrismIndexedConstant PolyadicallySOLLex Int
instance PrismPolyadicPredicate PolyadicallySOLLex Int Bool
instance PrismPolyadicFunction PolyadicallySOLLex Int Int
instance PrismPolyadicSchematicFunction PolyadicallySOLLex Int Int
instance PrismBooleanConnLex PolyadicallySOLLex Bool
instance PrismStandardQuant PolyadicallySOLLex Bool Int
instance PrismTermEquality PolyadicallySOLLex Int Bool

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
                 else SOAbstract (SOLam $ show v) (\x -> subBoundVar v x l)
incLam _ l v = SOAbstract (SOLam $ show v) (\x -> subBoundVar v x l)

incVar :: Typeable a => PolyadicallySOL (Form a) -> PolyadicallySOL (Form (Int -> a))
incVar ((SOPApp SOApp) :!$: l :!$: t) = (SOPApp SOApp) :!$: (incVar l) :!$: t
incVar (SOPVar s a) = SOPVar s (ASucc a)
incVar _ = error "attempted to increment the variable of a nonvariable predication"

incScheme :: Typeable a => PolyadicallySOL (Form a) -> PolyadicallySOL (Form (Int -> a))
incScheme ((SOPApp SOApp) :!$: l :!$: t) = (SOPApp SOApp) :!$: (incScheme l) :!$: t
incScheme (SOPScheme s a) = SOPScheme s (ASucc a)
incScheme _ = error "attempted to increment the variable of a nonvariable predication"

incQuant :: PolyadicallySOL (Form Bool) -> PolyadicallySOL (Form Bool)
incQuant ((SOPQuant (SOPAll s a)) :!$: (LLam f)) = 
    (SOPQuant (SOPAll s (ASucc a))) :!$: (LLam $ \x -> subBoundVar (SOPVar s (ASucc a)) x (f $ SOPVar s a))
incQuant ((SOPQuant (SOPSome s a)) :!$: (LLam f)) = 
    (SOPQuant (SOPSome s (ASucc a))) :!$: (LLam $ \x -> subBoundVar (SOPVar s (ASucc a)) x (f $ SOPVar s a))
incQuant _ = error "attempted to increment the quantifier of an unquantified sentence"

--increment the context of a higher-order variable
incVarCtx :: PolyadicallySOL (Form Bool) -> PolyadicallySOL (Form Bool)
incVarCtx ((SOPCtx n a) :!$: (SOPVar s c)) = (SOPCtx n (ASucc a)) :!$: (SOPVar s (ASucc c))
incVarCtx _ = error "attempted to increment the variable context of a non-variable/context predicaton"

--increment the context of a higher-order schematic variable
incSchemeCtx :: PolyadicallySOL (Form Bool) -> PolyadicallySOL (Form Bool)
incSchemeCtx ((SOPCtx n a) :!$: (SOPScheme s c)) = (SOPCtx n (ASucc a)) :!$: (SOPScheme s (ASucc c))
incSchemeCtx _ = error "attempted to increment the scheme context of a non-scheme/context predicaton"

--Determine whether a formula is a simple predication with a polyadic variable head
psolVarHead :: PolyadicallySOL a -> Bool
psolVarHead ((SOPApp SOApp) :!$: x) = psolVarHead x
psolVarHead (x :!$: _) = psolVarHead x
psolVarHead (SOPVar _ _) = True
psolVarHead _ = False

msolVarHead :: MonadicallySOL a -> Bool
msolVarHead ((SOMApp SOApp) :!$: x) = msolVarHead x
msolVarHead (x :!$: _) = msolVarHead x
msolVarHead (SOMVar _) = True
msolVarHead _ = False

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
