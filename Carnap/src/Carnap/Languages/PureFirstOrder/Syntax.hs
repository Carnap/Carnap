{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.PureFirstOrder.Syntax 
where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (Plated)
import Control.Lens.Fold (anyOf)
import Control.Lens.Plated (cosmos, transform)
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------------
--1. Data for Pure First Order Logic
--------------------------------------------------------

data PureMonadicPredicate a where
    MonPred :: Int -> PureMonadicPredicate Int

type PurePredicate = IntPred Bool Int

type PureConn = BooleanConn Bool

type PureSchematicPred = SchematicIntPred Bool Int

type PureConstant = IntConst Int

type PureVar = StandardVar Int

type PureQuant = StandardQuant Bool Int

--------------------------------------------------------
--2. Pure First Order Languages 
--------------------------------------------------------

--------------------------------------------------------
--2.1 Polyadic First Order Logic With Constant Symbols
--------------------------------------------------------

type PureFirstOrderLexicon = (Predicate PurePredicate
                       :|: Predicate PureSchematicPred
                       :|: Connective PureConn
                       :|: Quantifiers PureQuant
                       :|: SubstitutionalVariable
                       :|: Function PureConstant
                       :|: Function PureVar
                       :|: EndLang)

type PureFirstOrderLanguage = FixLang PureFirstOrderLexicon

type PureFOLForm = PureFirstOrderLanguage (Form Bool)

type PureFOLTerm = PureFirstOrderLanguage (Term Int)

pattern (:!!$:) :: (Typeable a, Typeable b) => PureFirstOrderLanguage (a -> b) -> PureFirstOrderLanguage a -> PureFirstOrderLanguage b
pattern (:!!$:) f y    = f :!$: y
pattern PPred x arity  = Fx1 (Predicate x arity)
pattern PSPred x arity = Fx2 (Predicate x arity)
pattern PCon x arity   = Fx3 (Connective x arity)
pattern PQuant q       = Fx4 (Bind q)
pattern PSV n          = Fx5 (SubVar n)
pattern PConst c a     = Fx6 (Function c a)
pattern PVar c a       = Fx7 (Function c a)
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern PBind q f      = PQuant q :!!$: LLam f
pattern PP n a1 a2     = PPred (Pred a1 n) a2
pattern PS :: Int -> PureFOLForm
pattern PS n           = PPred (Pred AZero n) AZero
pattern PC :: Int -> PureFOLTerm
pattern PC n           = PConst (Constant n) AZero
pattern PV s           = PVar (Var s) AZero
pattern PPhi n a1 a2   = PSPred (SPred a1 n) a2
pattern (:&:) x y      = PAnd :!!$: x :!!$: y
pattern (:||:) x y     = POr  :!!$: x :!!$: y
pattern (:->:) x y     = PIf  :!!$: x :!!$: y
pattern (:<->:) x y    = PIff :!!$: x :!!$: y
pattern PNeg x         = PNot :!!$: x
pattern PUniv v f      = PBind (All v) f
pattern PExist v f     = PBind (Some v) f
pattern PZero :: Arity (Term Int) (Form Bool) 'Zero (Form Bool)
pattern PZero          = AZero 

instance BooleanLanguage PureFOLForm where
        land = (:&:)
        lneg = PNeg
        lor  = (:||:)
        lif  = (:->:)
        liff = (:<->:)

instance IndexedPropLanguage PureFOLForm where
    pn = PS

instance PolyadicPredicateLanguage PureFirstOrderLanguage (Term Int) (Form Bool) where 
    ppn n a = PP n a a

incPred :: Typeable b => PureFirstOrderLanguage (Term Int -> b) -> Maybe (PureFirstOrderLanguage (Term Int -> Term Int -> b))
incPred = incArity incHead 
    where incHead (PP n a b) = Just $ PP n (ASucc a) (ASucc a)
          incPred _  = Nothing

instance QuantLanguage PureFOLForm PureFOLTerm where
        lall  = PUniv 
        lsome  = PExist 

instance CanonicalForm PureFOLForm where
    canonical = relabelVars varStream
                where varStream = [i ++ j | i <- ["x"], j <- map show [1 ..]]

instance CanonicalForm PureFOLTerm

instance BoundVars PureFirstOrderLexicon where
    getBoundVar (PQuant (All v)) _ = PV v
    getBoundVar (PQuant (Some v)) _ = PV v
    getBoundVar _ _ = undefined

    getBindHeight (PQuant (All v)) (LLam f) = PV $ show $ height (f $ PV "" )
    getBindHeight (PQuant (Some v)) (LLam f) = PV $ show $ height (f $ PV "" )
    getBindHeight _ _ = undefined

    subBoundVar a b (phi :&: psi)   = subBoundVar a b phi :&: subBoundVar a b psi
    subBoundVar a b (phi :||: psi)  = subBoundVar a b phi :||: subBoundVar a b psi
    subBoundVar a b (phi :->: psi)  = subBoundVar a b phi :||: subBoundVar a b psi
    subBoundVar a b (phi :<->: psi) = subBoundVar a b phi :||: subBoundVar a b psi
    subBoundVar a@(PV w) b (PUniv v f) = PUniv v (\x -> subBoundVar sv x $ subBoundVar a b $ f sv)
        where sv = case getBindHeight (PQuant (All v)) (LLam f) of
                           c@(PV v') -> if w == v' then PV ('_':v') else c
    subBoundVar a@(PV w) b (PExist v f) = PUniv v (\x -> subBoundVar sv x $ subBoundVar a b $ f sv)
        where sv = case getBindHeight (PQuant (All v)) (LLam f) of
                       c@(PV v') -> if w == v' then PV ('_':v') else c
    subBoundVar a b phi = mapover (swap a b) phi 

mapover :: (forall a . PureFirstOrderLanguage a -> PureFirstOrderLanguage a) -> PureFirstOrderLanguage a -> PureFirstOrderLanguage a
mapover f (x :!!$: y) = mapover f x :!!$: f y
mapover f x = x

swap :: PureFirstOrderLanguage b -> PureFirstOrderLanguage b -> PureFirstOrderLanguage a -> PureFirstOrderLanguage a
swap a@(PV _) b@(PV _) x@(PV _) = if x == a then b else x
swap a b c = c

height :: PureFirstOrderLanguage b -> Int
height (PUniv _ g)     = height (g $ PV "") + 1
height (PExist _ g)    = height (g $ PV "") + 1
height (phi :&: psi)   = max (height phi) (height psi)
height (phi :||: psi)  = max (height phi) (height psi)
height (phi :->: psi)  = max (height phi) (height psi)
height (phi :<->: psi) = max (height phi) (height psi)
height _               = 0

instance LangTypes2 PureFirstOrderLexicon Term Int Form Bool

instance LangTypes2 PureFirstOrderLexicon Form Bool Term Int

instance RelabelVars PureFirstOrderLexicon Form Bool where
    subBinder (PUniv v f) y = Just $ PUniv y f 
    subBinder (PExist v f) y = Just $ PExist y f
    subBinder _ _ = Nothing

instance CopulaSchema PureFirstOrderLanguage where
    appSchema (PQuant (All x)) (LLam f) e = schematize (All x) (show (f $ PV x) : e)
    appSchema (PQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ PV x) : e)
    appSchema x y e = schematize x (show y : e)
