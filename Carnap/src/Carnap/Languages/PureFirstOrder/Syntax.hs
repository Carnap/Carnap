{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.PureFirstOrder.Syntax 
where

import Carnap.Core.Util 
import Control.Monad.State
import qualified Carnap.Languages.PurePropositional.Syntax as P
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.ClassicalSequent.Syntax
import Control.Lens (Traversal')
import Data.Typeable (Typeable)
import Data.List (intercalate)
import Carnap.Languages.Util.GenericConstructors

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

type PurePredicate = IntPred Bool Int

type PureFunction = IntFunc Int Int

type PureSchematicFunction = SchematicIntFunc Int Int

type PureEq = TermEq Bool Int

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

type CoreLexicon = P.PurePropLexicon
                   :|: Binders PureQuant
                   :|: Function PureConstant
                   :|: Function PureVar
                   :|: Function (SchematicIntFunc Int Int)
                   :|: EndLang

type PureFirstOrderLexWith a = CoreLexicon :|: a

type PureFirstOrderLanguageWith a = FixLang (PureFirstOrderLexWith a)

pattern PSent n        = FX (Lx1 (Lx1 (Lx1 (Predicate (Prop n) AZero))))
pattern PSPhi n        = FX (Lx1 (Lx1 (Lx2 (Predicate (SProp n) AZero))))
pattern PCon x arity   = FX (Lx1 (Lx1 (Lx3 (Connective x arity))))
pattern PSV n          = FX (Lx1 (Lx1 (Lx4 (StaticVar n))))
pattern PDV n          = FX (Lx1 (Lx1 (Lx4 (SubVar n))))
pattern PCtx n         = FX (Lx1 (Lx1 (Lx5 (Connective (Context n) AOne))))
pattern PVerum         = FX (Lx1 (Lx1 (Lx6 (Connective (Verum) AZero))))
pattern PFalsum        = FX (Lx1 (Lx1 (Lx6 (Connective (Falsum) AZero))))
pattern PQuant q       = FX (Lx1 (Lx2 (Bind q)))
pattern PConst c a     = FX (Lx1 (Lx3 (Function c a)))
pattern PVar c a       = FX (Lx1 (Lx4 (Function c a)))
pattern PTau c a       = FX (Lx1 (Lx5 (Function c a)))
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern PBind q f      = PQuant q :!$: LLam f
pattern (:&:) x y      = PAnd :!$: x :!$: y
pattern (:||:) x y     = POr  :!$: x :!$: y
pattern (:->:) x y     = PIf  :!$: x :!$: y
pattern (:<->:) x y    = PIff :!$: x :!$: y
pattern PNeg x         = PNot :!$: x
pattern PC n           = PConst (Constant n) AZero
pattern PV s           = PVar (Var s) AZero
pattern PT n           = PTau (SFunc AZero n) AZero

instance ( StaticVar (PureFirstOrderLanguageWith a)
         , Schematizable (a (PureFirstOrderLanguageWith a))
         ) => CopulaSchema (PureFirstOrderLanguageWith a) where 

    appSchema (PQuant (All x)) (LLam f) e = schematize (All x) (show (f $ PV x) : e)
    appSchema (PQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ PV x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (static (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (static (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    BoundVars (PureFirstOrderLexWith a) where

    scopeUniqueVar (PQuant (Some v)) (LLam f) = PV $ show $ scopeHeight (LLam f)
    scopeUniqueVar (PQuant (All v)) (LLam f)  = PV $ show $ scopeHeight (LLam f)
    scopeUniqueVar _ _ = undefined

    subBoundVar = subst

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    LangTypes2 (PureFirstOrderLexWith a) Term Int Form Bool

termsOf :: FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
        Traversal' (FixLang (PureFirstOrderLexWith a) (Form Bool)) (FixLang (PureFirstOrderLexWith a) (Term Int))
termsOf = difChildren2

formsOf :: FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
        Traversal' (FixLang (PureFirstOrderLexWith a) (Form Bool)) (FixLang (PureFirstOrderLexWith a) (Form Bool))
formsOf = simChildren2

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    LangTypes2 (PureFirstOrderLexWith a) Form Bool Term Int

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    RelabelVars (PureFirstOrderLexWith a) Form Bool where

    subBinder (PBind (All v) f) y = Just $ PBind (All y) f 
    subBinder (PBind (Some v) f) y = Just $ PBind (Some y) f
    subBinder _ _ = Nothing

instance FirstOrder (FixLang (PureFirstOrderLexWith a)) => 
    CanonicalForm (PureFirstOrderLanguageWith a (Form Bool)) where

    canonical = relabelVars varStream
                where varStream = [i ++ j | i <- ["x"], j <- map show [1 ..]]

instance CanonicalForm (PureFirstOrderLanguageWith a (Term Int))

instance PrismPropLex (PureFirstOrderLexWith a) Bool
instance PrismIndexedConstant (PureFirstOrderLexWith a) Int
instance PrismBooleanConnLex (PureFirstOrderLexWith a) Bool
instance PrismPropositionalContext (PureFirstOrderLexWith a) Bool
instance PrismBooleanConst (PureFirstOrderLexWith a) Bool
instance PrismSchematicProp (PureFirstOrderLexWith a) Bool
instance PrismStandardQuant (PureFirstOrderLexWith a) Bool Int

--equality up to α-equivalence
instance UniformlyEq (PureFirstOrderLanguageWith a) => Eq (PureFirstOrderLanguageWith a b) where
        (==) = (=*)
    
--------------------------------------------------------
--2.1 Monadic First Order Logic
--------------------------------------------------------

--Note that we *could* add monadic function symbols and identity while
--preserving decidability

type MonadicPredicates = Predicate PureMonadicPredicate :|: EndLang

type OpenLexiconMFOL a = CoreLexicon :|: MonadicPredicates :|: a

type PureLexiconMFOL = OpenLexiconMFOL EndLang

type OpenLanguageMFOL a = FixLang (OpenLexiconMFOL a)

type PureLanguageMFOL = FixLang PureLexiconMFOL

pattern PMPred n = FX (Lx2 (Lx1 (Predicate (MonPred n) AOne)))

type OpenMFOLForm a = OpenLanguageMFOL a (Form Bool)

type PureMFOLForm = OpenMFOLForm EndLang

type OpenMFOLTerm a = OpenLanguageMFOL a (Term Int)

type PureMFOLTerm = OpenMFOLTerm EndLang

--------------------------------------------------------
--2.2 Polyadic First Order Logic
--------------------------------------------------------

type PolyadicPredicates = Predicate PurePredicate 
                      :|: Predicate PureSchematicPred
                      :|: EndLang

type OpenLexiconPFOL a = CoreLexicon :|: PolyadicPredicates :|: a

type PureLexiconPFOL = OpenLexiconPFOL EndLang

type OpenLanguagePFOL a = FixLang (OpenLexiconPFOL a)

type PureLanguagePFOL = FixLang PureLexiconPFOL

pattern PPred x arity  = FX (Lx2 (Lx1 (Predicate x arity)))
pattern PSPred x arity = FX (Lx2 (Lx2 (Predicate x arity)))
pattern PP n a1 a2     = PPred (Pred a1 n) a2
pattern PPhi n a1 a2   = PSPred (SPred a1 n) a2

type OpenPFOLForm a = OpenLanguagePFOL a (Form Bool)

type PurePFOLForm = OpenPFOLForm EndLang

type OpenPFOLTerm a = OpenLanguagePFOL a (Term Int)

type PurePFOLTerm = OpenPFOLTerm EndLang

instance PrismPolyadicPredicate (OpenLexiconPFOL a) Int Bool
instance PrismPolyadicSchematicPredicate (OpenLexiconPFOL a) Int Bool

instance Incrementable (OpenLexiconPFOL EndLang) (Term Int) where
    incHead (PP n a b)   = Just $ PP n (ASucc a) (ASucc a)
    incHead (PPhi n a b) = Just $ PPhi n (ASucc a) (ASucc a)
    incHead _  = Nothing

--------------------------------------------------------
--2.3 Polyadic First Order Logic with Polyadic Function Symbols and Identity
--------------------------------------------------------

type PolyadicFunctionSymbolsAndIdentity = Predicate PureEq 
                                        :|: Function PureFunction 
                                        :|: Function PureSchematicFunction
                                        :|: EndLang

type PureLexiconFOL = (OpenLexiconPFOL (PolyadicFunctionSymbolsAndIdentity :|: EndLang))

type PureLanguageFOL = FixLang PureLexiconFOL

fogamma :: Int -> ClassicalSequentOver PureLexiconFOL (Antecedent (Form Bool))
fogamma n = GammaV n

pattern PEq            = FX (Lx3 (Lx1 (Predicate TermEq ATwo)))
pattern (:==:) t1 t2   = PEq :!$: t1 :!$: t2
pattern PFunc x arity  = FX (Lx3 (Lx2 (Function x arity)))
pattern PSFunc x arity  = FX (Lx3 (Lx3 (Function x arity)))
pattern PF n a1 a2     = PFunc (Func a1 n) a2
pattern PSF n a1 a2    = PSFunc (SFunc a1 n) a2

type PureFOLForm = PureLanguageFOL (Form Bool)

type PureFOLTerm = PureLanguageFOL (Term Int)

instance PrismTermEquality PureLexiconFOL Int Bool
instance PrismPolyadicFunction PureLexiconFOL Int Int
instance PrismPolyadicSchematicFunction PureLexiconFOL Int Int

instance Incrementable (OpenLexiconPFOL (PolyadicFunctionSymbolsAndIdentity :|: a)) (Term Int) where
    incHead (PP n a b)   = Just $ PP n (ASucc a) (ASucc a)
    incHead (PF n a b)   = Just $ PF n (ASucc a) (ASucc a)
    incHead (PSF n a b)  = Just $ PSF n (ASucc a) (ASucc a)
    incHead (PPhi n a b) = Just $ PPhi n (ASucc a) (ASucc a)
    incHead _  = Nothing
