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
import Carnap.Languages.Util.GenericConnectives
import Data.List (intercalate)

--------------------------------------------------------
--1. Data for Monadic Second Order Logic
--------------------------------------------------------

data MonadicSOVar a where
        MonVar :: String -> MonadicSOVar (Form (Int -> Bool))

instance Schematizable MonadicSOVar where
        schematize (MonVar s) = const s

instance UniformlyEq MonadicSOVar where
    (MonVar n) =* (MonVar m) = n == m

instance Monad m => MaybeMonadVar MonadicSOVar m

instance MaybeStaticVar MonadicSOVar

instance FirstOrderLex MonadicSOVar

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
        schematize (SOApp)  = \(x:y:_) -> if last x == ')' then init x ++ "," ++ y  ++ ")"
                                                           else x ++ "(" ++ y ++ ")"

instance UniformlyEq SOApplicator where
    (SOApp) =* (SOApp) = True

instance Monad m => MaybeMonadVar SOApplicator m

instance MaybeStaticVar SOApplicator

instance FirstOrderLex SOApplicator

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

--------------------------------------------------------
--2. Monadic Second Order Logic
--------------------------------------------------------

type MonadicallySOLLex = FOL.PureLexiconFOL
                        :|: Predicate MonadicSOVar
                        :|: Quantifiers MonadicSOQuant
                        :|: Abstractors SOLambda
                        :|: Applicators SOApplicator
                        :|: EndLang

type MonadicallySOL = FixLang MonadicallySOLLex


pattern SOSent n        = FX (Lx1 (Lx1 (Lx1 (Lx1 (Predicate (Prop n) AZero)))))
pattern SOSPhi n        = FX (Lx1 (Lx1 (Lx1 (Lx2 (Predicate (SProp n) AZero)))))
pattern SOCon x arity   = FX (Lx1 (Lx1 (Lx1 (Lx3 (Connective x arity)))))
pattern SOSV n          = FX (Lx1 (Lx1 (Lx1 (Lx4 (StaticVar n)))))
pattern SODV n          = FX (Lx1 (Lx1 (Lx1 (Lx4 (SubVar n)))))
pattern SOQuant q       = FX (Lx1 (Lx1 (Lx2 (Bind q))))
pattern SOConst c a     = FX (Lx1 (Lx1 (Lx3 (Function c a))))
pattern SOVar c a       = FX (Lx1 (Lx1 (Lx4 (Function c a))))
pattern SOTau c a       = FX (Lx1 (Lx1 (Lx5 (Function c a))))
pattern SOPred x arity   = FX (Lx1 (Lx2 (Lx1 (Predicate x arity))))
pattern SOSPred x arity = FX (Lx1 (Lx2 (Lx2 (Predicate x arity))))
pattern SOFunc x arity  = FX (Lx1 (Lx3 (Lx2 (Function x arity))))
pattern SOMVar n        = FX (Lx2 (Predicate (MonVar n) AZero))
pattern SOMQuant q      = FX (Lx3 (Bind q))
pattern SOMAbs a        = FX (Lx4 (Abstract a))
pattern SOMApp a        = FX (Lx5 (Apply a))
pattern SOP n a1 a2     = SOPred (Pred a1 n) a2
pattern SOPhi n a1 a2   = SOPred (SPred a1 n) a2
pattern SOAnd           = SOCon And ATwo
pattern SOOr            = SOCon Or ATwo
pattern SOIf            = SOCon If ATwo
pattern SOIff           = SOCon Iff ATwo
pattern SONot           = SOCon Not AOne
pattern SOAbstract l f  = SOMAbs l :!$: LLam f
pattern SOBind q f      = SOQuant q :!$: LLam f
pattern SOMBind q f     = SOMQuant q :!$: LLam f
pattern (:&:) x y       = SOAnd :!$: x :!$: y
pattern (:||:) x y      = SOOr  :!$: x :!$: y
pattern (:->:) x y      = SOIf  :!$: x :!$: y
pattern (:<->:) x y     = SOIff :!$: x :!$: y
pattern SONeg x         = SONot :!$: x
pattern SOC n           = SOConst (Constant n) AZero
pattern SOV s           = SOVar (Var s) AZero
pattern SOT n           = SOTau (SFunc AZero n) AZero
pattern SOEq            = FX (Lx1 (Lx3 (Lx1 (Predicate TermEq ATwo))))
pattern (:==:) t1 t2    = SOEq :!$: t1 :!$: t2
pattern SOF n a1 a2     = SOFunc (Func a1 n) a2

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
    incHead (SOF n a b) = Just $ SOF n (ASucc a) (ASucc a)
    incHead _  = Nothing

instance BoundVars MonadicallySOLLex where

    scopeUniqueVar (SOQuant (Some v)) (LLam f) = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar (SOQuant (All v)) (LLam f)  = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance PolyadicPredicateLanguage MonadicallySOL (Term Int) (Form Bool) 
    where ppn n a = SOP n a a

instance PolyadicFunctionLanguage MonadicallySOL (Term Int) (Term Int) where 
    pfn n a = SOF n a a

instance IndexedPropLanguage (MonadicallySOL (Form Bool)) where
    pn = SOSent

instance IndexedConstantLanguage (MonadicallySOL(Term Int)) where 
        cn = SOC

instance BooleanLanguage (MonadicallySOL (Form Bool)) where
    land = (:&:)
    lneg = SONeg
    lor  = (:||:)
    lif  = (:->:)
    liff = (:<->:)

instance QuantLanguage (MonadicallySOL (Form Bool)) (MonadicallySOL (Term Int)) where
    lall  v f = SOQuant (All v) :!$: LLam f
    lsome  v f = SOQuant (Some v) :!$: LLam f

instance QuantLanguage (MonadicallySOL (Form Bool)) (MonadicallySOL (Form (Int -> Bool))) where
    lall  v f = SOMQuant (SOAll v) :!$: LLam f
    lsome  v f = SOMQuant (SOSome v) :!$: LLam f

--------------------------------------------------------
--3. Data for Polyadic SOL
--------------------------------------------------------

data PolySOLVar a where
        PolyVar :: String -> Arity Int Bool n t -> PolySOLVar (Form t)

instance Schematizable PolySOLVar where
        schematize (PolyVar s a) = const s

instance UniformlyEq PolySOLVar where
    (PolyVar n a) =* (PolyVar m a') = n == m && show a == show a'

instance Monad m => MaybeMonadVar PolySOLVar m

instance MaybeStaticVar PolySOLVar

instance FirstOrderLex PolySOLVar

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
--3. Polyadic SOL
--------------------------------------------------------

type PolyadicallySOLLex = FOL.PureLexiconFOL
                        :|: Predicate PolySOLVar
                        :|: Quantifiers PolySOLQuant
                        :|: Abstractors SOLambda
                        :|: Applicators SOApplicator
                        :|: EndLang

type PolyadicallySOL = FixLang PolyadicallySOLLex

pattern SOPVar n a      = FX (Lx2 (Predicate (PolyVar n a) AZero))
pattern SOPQuant q      = FX (Lx3 (Bind q))
pattern SOPAbs a        = FX (Lx4 (Abstract a))
pattern SOPApp a        = FX (Lx5 (Apply a))
pattern SOPBind q f     = SOPQuant q :!$: LLam f

instance Incrementable PolyadicallySOLLex (Term Int) where
    incHead (SOP n a b) = Just $ SOP n (ASucc a) (ASucc a)
    incHead (SOF n a b) = Just $ SOF n (ASucc a) (ASucc a)
    incHead _  = Nothing

instance BoundVars PolyadicallySOLLex where

    scopeUniqueVar (SOQuant (Some v)) (LLam f) = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar (SOQuant (All v)) (LLam f)  = SOV $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance PolyadicPredicateLanguage PolyadicallySOL (Term Int) (Form Bool) 
    where ppn n a = SOP n a a

instance PolyadicFunctionLanguage PolyadicallySOL (Term Int) (Term Int) where 
    pfn n a = SOF n a a

instance IndexedPropLanguage (PolyadicallySOL (Form Bool)) where
    pn = SOSent

instance IndexedConstantLanguage (PolyadicallySOL (Term Int)) where 
        cn = SOC

instance BooleanLanguage (PolyadicallySOL (Form Bool)) where
    land = (:&:)
    lneg = SONeg
    lor  = (:||:)
    lif  = (:->:)
    liff = (:<->:)

instance QuantLanguage (PolyadicallySOL (Form Bool)) (PolyadicallySOL (Term Int)) where
    lall  v f = SOQuant (All v) :!$: LLam f
    lsome  v f = SOQuant (Some v) :!$: LLam f

instance CopulaSchema PolyadicallySOL where 

    appSchema (SOQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SOV x) : e)
    appSchema (SOQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SOV x) : e)
    appSchema (SOPQuant (SOPAll x a)) (LLam f) e = schematize (SOPAll x a) (show (f $ SOPVar x a) : e)
    appSchema (SOPQuant (SOPSome x a)) (LLam f) e = schematize (SOPSome x a) (show (f $ SOPVar x a) : e)
    appSchema (SOMAbs (SOLam v)) (LLam f) e = schematize (SOLam v) (show (f $ SOV v) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

--------------------------------------------------------
--Notes
--------------------------------------------------------

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

where κ can be any lambda term. No idea if this will typecheck, but it
doesn't feel good. It does feel like the requirement of a polymorphic type for lambda terms is unavoidable.



--}
