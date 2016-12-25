{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Languages.PureSecondOrder.Syntax
where


import Carnap.Core.Util 
import Carnap.Languages.PureFirstOrder.Syntax as FOL
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConnectives
import Data.List (intercalate)

--------------------------------------------------------
--1. Data for Monadically Second Order Logic
--------------------------------------------------------

data MonadicSOVar a where
        MonVar :: String -> MonadicSOVar (Term Int -> Form Bool)

instance Schematizable MonadicSOVar where
        schematize (MonVar s) = \(x:xs) -> s ++ "(" ++ x ++ ")"

instance UniformlyEq MonadicSOVar where
    (MonVar n) =* (MonVar m) = n == m

instance Monad m => MaybeMonadVar MonadicSOVar m

instance MaybeStaticVar MonadicSOVar

instance FirstOrderLex MonadicSOVar

data MonadicSOQuant a where
        SOAll :: String -> 
            MonadicSOQuant (((Term Int -> Form Bool) -> Form Bool) -> Form Bool)
        SOSome :: String -> 
            MonadicSOQuant (((Term Int -> Form Bool) -> Form Bool) -> Form Bool)

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
pattern PPred x arity   = FX (Lx1 (Lx2 (Lx1 (Predicate x arity))))
pattern SOSPred x arity = FX (Lx1 (Lx2 (Lx2 (Predicate x arity))))
pattern SOFunc x arity  = FX (Lx1 (Lx3 (Lx2 (Function x arity))))
pattern SOMVar n        = FX (Lx2 (Predicate (MonVar n) AOne))
pattern SOMQuant q      = FX (Lx3 (Bind q))
pattern SOPred x arity  = FX (Lx1 (Lx2 (Lx1 (Predicate x arity))))
pattern SOP n a1 a2     = SOPred (Pred a1 n) a2
pattern SOPhi n a1 a2   = PSPred (SPred a1 n) a2
pattern SOAnd           = SOCon And ATwo
pattern SOOr            = SOCon Or ATwo
pattern SOIf            = SOCon If ATwo
pattern SOIff           = SOCon Iff ATwo
pattern SONot           = SOCon Not AOne
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
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SOSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)
