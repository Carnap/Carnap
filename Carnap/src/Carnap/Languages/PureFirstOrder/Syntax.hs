{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.PureFirstOrder.Syntax 
where

import Carnap.Core.Util 
import Control.Monad.State
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (Traversal')
import Data.Typeable (Typeable)
import Data.List (intercalate)
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------------
--1. Data for Pure First Order Logic
--------------------------------------------------------

data PureMonadicPredicate a where
    MonPred :: Int -> PureMonadicPredicate (Term Int -> Form Bool)

instance Schematizable PureMonadicPredicate where
    schematize (MonPred n) = \(x:xs) -> "P_" ++ show n ++ "(" ++ x ++ ")"

instance UniformlyEq PureMonadicPredicate where
    (MonPred n) =* (MonPred m) = n == m

instance FirstOrderLex PureMonadicPredicate 

instance Monad m => MaybeMonadVar PureMonadicPredicate m

instance MaybeStaticVar PureMonadicPredicate

data PureSentences a where
    Sent :: Int -> PureSentences (Form Bool)

instance Schematizable PureSentences where
    schematize (Sent n) = const $ "P_" ++ show n

instance UniformlyEq (PureSentences) where
    (Sent n) =* (Sent m) = n == m

instance FirstOrderLex PureSentences

instance Monad m => MaybeMonadVar PureSentences m

instance MaybeStaticVar PureSentences

type PurePredicate = IntPred Bool Int

type PureFunction = IntFunc Int Int

type PureEq = TermEq Bool Int

type PureConn = BooleanConn Bool

type PureSchematicPred = SchematicIntPred Bool Int

type PureConstant = IntConst Int

type PureVar = StandardVar Int

type PureQuant = StandardQuant Bool Int

--------------------------------------------------------
--2. Pure First Order Languages 
--------------------------------------------------------

--------------------------------------------------------
--2.0 Common Core of FOL
--------------------------------------------------------

type CoreLexicon =  Connective PureConn
                   :|: Quantifiers PureQuant
                   :|: SubstitutionalVariable
                   :|: Function PureConstant
                   :|: Function PureVar
                   :|: EndLang

type PureFirstOrderLanguageWith a = FixLang (CoreLexicon :|: a)

pattern (:!!$:) :: (Typeable a, Typeable b) => PureFirstOrderLanguageWith c (a -> b) -> PureFirstOrderLanguageWith c a -> PureFirstOrderLanguageWith c b
pattern (:!!$:) f y    = f :!$: y
pattern PCon x arity   = FX (Lx1 (Lx1 (Connective x arity)))
pattern PQuant q       = FX (Lx1 (Lx2 (Bind q)))
pattern PSV n          = FX (Lx1 (Lx3 (SubVar n)))
pattern PConst c a     = FX (Lx1 (Lx4 (Function c a)))
pattern PVar c a       = FX (Lx1 (Lx5 (Function c a)))
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern PBind q f      = PQuant q :!!$: LLam f
pattern (:&:) x y      = PAnd :!!$: x :!!$: y
pattern (:||:) x y     = POr  :!!$: x :!!$: y
pattern (:->:) x y     = PIf  :!!$: x :!!$: y
pattern (:<->:) x y    = PIff :!!$: x :!!$: y
pattern PNeg x         = PNot :!!$: x
pattern PUniv v f      = PBind (All v) f
pattern PExist v f     = PBind (Some v) f
pattern PC n           = PConst (Constant n) AZero
pattern PV s           = PVar (Var s) AZero

-- height :: PureFirstOrderLanguageWith a b -> Int
-- height (PUniv _ g)     = height (g $ PV "") + 1
-- height (PExist _ g)    = height (g $ PV "") + 1
-- height (phi :&: psi)   = max (height phi) (height psi)
-- height (phi :||: psi)  = max (height phi) (height psi)
-- height (phi :->: psi)  = max (height phi) (height psi)
-- height (phi :<->: psi) = max (height phi) (height psi)
-- height _               = 0

instance Schematizable (a (PureFirstOrderLanguageWith a)) => 
    CopulaSchema (PureFirstOrderLanguageWith a) where 

    appSchema (PQuant (All x)) (LLam f) e = schematize (All x) (show (f $ PV x) : e)
    appSchema (PQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ PV x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λα_" ++ show h ++ "." ++ show (f (PSV h))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λα_" ++ show h ++ "." ++ show (f (PSV h)) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

instance FirstOrder (FixLang (CoreLexicon :|: a)) => 
    BoundVars (CoreLexicon :|: a) where

    scopeUniqueVar (PQuant (Some v)) (LLam f) = PV $ show $ scopeHeight (LLam f)
    scopeUniqueVar (PQuant (All v)) (LLam f)  = PV $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance FirstOrder (FixLang (CoreLexicon :|: a)) => 
    LangTypes2 (CoreLexicon :|: a) Term Int Form Bool

termsOf :: FirstOrder (FixLang (CoreLexicon :|: a)) => 
        Traversal' (FixLang (CoreLexicon :|: a) (Form Bool)) (FixLang (CoreLexicon :|: a) (Term Int))
termsOf = difChildren2

instance FirstOrder (FixLang (CoreLexicon :|: a)) => 
    LangTypes2 (CoreLexicon :|: a) Form Bool Term Int

instance BooleanLanguage (PureFirstOrderLanguageWith a (Form Bool)) where
    land = (:&:)
    lneg = PNeg
    lor  = (:||:)
    lif  = (:->:)
    liff = (:<->:)

instance QuantLanguage (PureFirstOrderLanguageWith a (Form Bool)) (PureFirstOrderLanguageWith a (Term Int)) where
    lall  = PUniv 
    lsome  = PExist 

instance FirstOrder (FixLang (CoreLexicon :|: a)) => 
    RelabelVars (CoreLexicon :|: a) Form Bool where

    subBinder (PUniv v f) y = Just $ PUniv y f 
    subBinder (PExist v f) y = Just $ PExist y f
    subBinder _ _ = Nothing

instance FirstOrder (FixLang (CoreLexicon :|: a)) => 
    CanonicalForm (PureFirstOrderLanguageWith a (Form Bool)) where

    canonical = relabelVars varStream
                where varStream = [i ++ j | i <- ["x"], j <- map show [1 ..]]

instance CanonicalForm (PureFirstOrderLanguageWith a (Term Int))

instance IndexedConstantLanguage (PureFirstOrderLanguageWith a (Term Int)) where 
        cn = PC

--equality up to α-equivalence
instance UniformlyEq (PureFirstOrderLanguageWith a) => Eq (PureFirstOrderLanguageWith a b) where
        (==) = (=*)
    
--------------------------------------------------------
--2.1 Monadic First Order Logic
--------------------------------------------------------

type MonadicPredicates = Predicate PureMonadicPredicate
                      :|: Predicate PureSentences
                      :|: EndLang

type OpenLexiconMFOL a = CoreLexicon :|: MonadicPredicates :|: a

type OpenLanguageMFOL a = FixLang (OpenLexiconMFOL a)

type PureLanguageMFOL = OpenLanguageMFOL EndLang

pattern PMPred n = FX (Lx2 (Lx1 (Predicate (MonPred n) AOne)))
pattern PMSent n = FX (Lx2 (Lx2 (Predicate (Sent n) AZero)))

type OpenMFOLForm a = OpenLanguageMFOL a (Form Bool)

type PureMFOLForm = OpenMFOLForm EndLang

type OpenMFOLTerm a = OpenLanguageMFOL a (Term Int)

type PureMFOLTerm = OpenMFOLTerm EndLang

instance IndexedPropLanguage (OpenMFOLForm a) where
    pn = PMSent

--------------------------------------------------------
--2.2 Polyadic First Order Logic
--------------------------------------------------------

type PolyadicPredicates = Predicate PurePredicate 
                      :|: Predicate PureSchematicPred
                      :|: EndLang

type OpenLexiconPFOL a = CoreLexicon :|: PolyadicPredicates :|: a

type OpenLanguagePFOL a = FixLang (OpenLexiconPFOL a)

type PureLanguagePFOL = OpenLanguagePFOL EndLang

pattern PPred x arity  = FX (Lx2 (Lx1 (Predicate x arity)))
pattern PSPred x arity = FX (Lx2 (Lx2 (Predicate x arity)))
pattern PP n a1 a2     = PPred (Pred a1 n) a2
pattern PS n           = PPred (Pred AZero n) AZero
pattern PPhi n a1 a2   = PSPred (SPred a1 n) a2

type OpenPFOLForm a = OpenLanguagePFOL a (Form Bool)

type PurePFOLForm = OpenPFOLForm EndLang

type OpenPFOLTerm a = OpenLanguagePFOL a (Term Int)

type PurePFOLTerm = OpenPFOLTerm EndLang

instance IndexedPropLanguage (OpenPFOLForm a) where
    pn = PS

instance PolyadicPredicateLanguage (OpenLanguagePFOL a) (Term Int) (Form Bool) 
    where ppn n a = PP n a a

instance Incrementable (OpenLexiconPFOL EndLang) (Term Int) where
    incHead (PP n a b) = Just $ PP n (ASucc a) (ASucc a)
    incHead _  = Nothing

--------------------------------------------------------
--2.3 Polyadic First Order Logic with Polyadic Function Symbols and Identity
--------------------------------------------------------

type PolyadicFunctionSymbolsAndIdentity = Predicate PureEq :|: Function PureFunction :|: EndLang

type PureLexiconFOL = (OpenLexiconPFOL (PolyadicFunctionSymbolsAndIdentity :|: EndLang))

type PureLanguageFOL = FixLang PureLexiconFOL

pattern PEq = FX (Lx3 (Lx1 (Predicate TermEq ATwo)))
pattern (:==:) t1 t2 = PEq :!$: t1 :!$: t2
pattern PFunc x arity  = FX (Lx3 (Lx2 (Function x arity)))
pattern PF n a1 a2     = PFunc (Func a1 n) a2

type PureFOLForm = PureLanguageFOL (Form Bool)

type PureFOLTerm = PureLanguageFOL (Term Int)

instance EqLanguage PureFOLForm PureFOLTerm  where 
    equals = (:==:)

instance PolyadicFunctionLanguage PureLanguageFOL (Term Int) (Term Int) where 
    pfn n a = PF n a a

instance Incrementable (OpenLexiconPFOL (PolyadicFunctionSymbolsAndIdentity :|: a)) (Term Int) where
    incHead (PP n a b) = Just $ PP n (ASucc a) (ASucc a)
    incHead (PF n a b) = Just $ PF n (ASucc a) (ASucc a)
    incHead _  = Nothing
