{-#LANGUAGE FunctionalDependencies, FlexibleInstances, MultiParamTypeClasses, GADTs, KindSignatures, TypeOperators, PatternSynonyms, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.ModalPropositional.Syntax where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (checkChildren)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Carnap.Core.Data.Util (scopeHeight)
import Control.Lens.Plated (transform)
import Data.Typeable (Typeable)
import Data.List (intercalate)
import Data.Map.Lazy (Map, (!))
import qualified Data.Monoid as M
import Carnap.Languages.Util.GenericConstructors

--------------------------------------------------
--  1. Data for Pure Propositional Modal Logic  --
--------------------------------------------------

--the semantic values in this language are intensions rather than boolean
--values

type World = Int

type ModalProp = IntProp (World -> Bool)

type ModalSchematicPred = SchematicIntPred (World -> Bool) World

type ModalPropositionalContext = PropositionalContext (World -> Bool)

data PropFrame = PropFrame { valuation :: World -> Bool
                           , accessibility :: Map World [World]
                           }

instance Evaluable ModalProp where
        eval (Prop n) = Form $ const $ even n

instance Modelable PropFrame ModalProp where
        satisfies f (Prop n) = Form $ const $  valuation f n

type ModalConn = BooleanConn (World -> Bool)

instance Evaluable ModalConn where
        eval Iff = lift2 $ \f g x -> f x == g x
        eval If  = lift2 $ \f g x -> not (f x) || g x
        eval Or  = lift2 $ \f g x -> f x || g x
        eval And = lift2 $ \f g x -> f x && g x
        eval Not = lift1 $ \f x -> not $ f x

type ModalConst = BooleanConst (World -> Bool)

instance Modelable PropFrame ModalConn where
    satisfies = const eval

instance Evaluable ModalConst where
        eval Verum = Form (const True)
        eval Falsum = Form (const False)

instance Modelable PropFrame ModalConst where
    satisfies = const eval

type PropModality = Modality (World -> Bool)

--For the eval frame, we stipulate that the accessibility relation is empty
instance Evaluable PropModality where
        eval Box = lift1 $ \f -> const True
        eval Diamond = lift1 $ \f -> const False

instance Modelable PropFrame PropModality where
        satisfies f Box = lift1 $ \f x -> M.getAll $ mconcat (map (M.All . f) (ac x))
            where ac x = accessibility f ! x
        satisfies f Diamond = lift1 $ \f x -> M.getAny $ mconcat (map (M.Any . f) (ac x))
            where ac x = accessibility f ! x

type Index = IntIndex World

type IndexScheme = SchematicIntFunc World World

type ModalSchematicProp = SchematicIntProp (World -> Bool)

type WorldTheoryIndexer = Indexer World (World -> Bool) (World -> Bool)

type IndexVar = StandardVar World

type AbsoluteIndexer = Indexer World (World -> Bool) Bool

type IndexCons = Cons World

type IndexQuant = StandardQuant (World -> Bool) World

-------------------------------------------
--  2. Core Lexicon for Modal Languages  --
-------------------------------------------

type CoreLexicon = Predicate ModalProp
                   :|: Predicate ModalSchematicProp
                   :|: Connective ModalConn
                   :|: Connective PropModality
                   :|: Connective ModalConst
                   :|: SubstitutionalVariable
                   :|: Connective ModalPropositionalContext
                   :|: EndLang

instance PrismBooleanConnLex CoreLexicon (World -> Bool)
instance PrismGenericContext CoreLexicon (World -> Bool) (World -> Bool)
instance PrismBooleanConst CoreLexicon (World -> Bool)
instance PrismPropLex CoreLexicon (World -> Bool)
instance PrismSchematicProp CoreLexicon (World -> Bool)
instance PrismModality CoreLexicon (World -> Bool)

type ModalPropLexiconWith a = CoreLexicon :|: a :|: EndLang

type ModalPropLanguageWith a = FixLang (ModalPropLexiconWith a)

instance UniformlyEq (ModalPropLanguageWith a) => Eq (ModalPropLanguageWith a b) where
        (==) = (=*)

pattern MPred x arity  = FX (Lx1 (Lx1 (Predicate x arity)))
pattern MSPred x arity = FX (Lx1 (Lx2 (Predicate x arity)))
pattern MBCon x arity  = FX (Lx1 (Lx3 (Connective x arity)))
pattern MMCon x arity  = FX (Lx1 (Lx4 (Connective x arity)))
pattern MVerum         = FX (Lx1 (Lx5 (Connective (Verum) AZero)))
pattern MFalsum        = FX (Lx1 (Lx5 (Connective (Falsum) AZero)))
pattern MSV n          = FX (Lx1 (Lx6 (SubVar n)))
pattern MAnd           = MBCon And ATwo
pattern MOr            = MBCon Or ATwo
pattern MIf            = MBCon If ATwo
pattern MIff           = MBCon Iff ATwo
pattern MNot           = MBCon Not AOne
pattern MBox           = MMCon Box AOne
pattern MDiamond       = MMCon Diamond AOne
pattern MP n           = MPred (Prop n) AZero
pattern MPhi n         = MSPred (SProp n) AZero
pattern (:&:) x y      = MAnd :!$: x :!$: y
pattern (:||:) x y     = MOr :!$: x :!$: y
pattern (:->:) x y     = MIf :!$: x :!$: y
pattern (:<->:) x y    = MIff :!$: x :!$: y
pattern MNeg x         = MNot :!$: x
pattern MNec x         = MBox :!$: x
pattern MPos x         = MDiamond :!$: x

instance PrismBooleanConnLex (ModalPropLexiconWith a) (World -> Bool)
instance PrismGenericContext (ModalPropLexiconWith a) (World -> Bool) (World -> Bool)
instance PrismBooleanConst (ModalPropLexiconWith a) (World -> Bool)
instance PrismPropLex (ModalPropLexiconWith a) (World -> Bool)
instance PrismSchematicProp (ModalPropLexiconWith a) (World -> Bool)
instance PrismModality (ModalPropLexiconWith a) (World -> Bool)

-------------------------------
--  3. Basic Modal Language  --
-------------------------------

type ModalPropLexicon = ModalPropLexiconWith EndLang

instance BoundVars ModalPropLexicon

type ModalPropLanguage = FixLang ModalPropLexicon

instance LangTypes1 ModalPropLexicon Form (World -> Bool)

type ModalForm = ModalPropLanguage (Form (World -> Bool))

instance CopulaSchema ModalPropLanguage

--------------------------
--  4. World Languages  --
--------------------------

type WorldTheoryLexicon = WorldTheoryIndexer 
                        :|: Function Index
                        :|: Function IndexCons 
                        :|: Function IndexScheme
                        :|: Binders IndexQuant
                        :|: Predicate ModalSchematicPred
                        :|: Function IndexVar
                        :|: EndLang

type WorldTheoryPropLexicon = ModalPropLexiconWith WorldTheoryLexicon

type WorldTheoryPropLanguage = ModalPropLanguageWith WorldTheoryLexicon

pattern IQuant q = (FX (Lx2 (Lx5 (Bind q))))
pattern PSV n  = FX (Lx1 (Lx6 (StaticVar n)))

instance CopulaSchema WorldTheoryPropLanguage where
    appSchema (IQuant (All x)) (LLam f) e = schematize (All x) (show (f $ worldVar x) : e)
    appSchema (IQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ worldVar x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (PSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (PSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

instance BoundVars WorldTheoryPropLexicon where
        scopeUniqueVar (IQuant (All v)) (LLam f) = worldVar (show $ scopeHeight (LLam f))
        scopeUniqueVar (IQuant (Some v)) (LLam f) = worldVar (show $ scopeHeight (LLam f))

        subBoundVar = subst

type WorldTheoryForm = WorldTheoryPropLanguage (Form (World -> Bool))

instance PrismGenericQuant WorldTheoryPropLexicon Term Form (World -> Bool) World
instance PrismIndexing WorldTheoryPropLexicon World (World -> Bool) (World->Bool) 
instance PrismIntIndex WorldTheoryPropLexicon World
instance PrismCons WorldTheoryPropLexicon World
instance PrismPolyadicSchematicFunction WorldTheoryPropLexicon World World
instance PrismPolyadicSchematicPredicate WorldTheoryPropLexicon World (World -> Bool) 

----------------------------------------
--  5. Absolute Modal Logic Language  --
----------------------------------------

type AbsoluteModalLexicon = AbsoluteIndexer
                        :|: Function Index
                        :|: Function IndexCons 
                        :|: Function IndexScheme
                        :|: EndLang

type AbsoluteModalPropLexicon = ModalPropLexiconWith AbsoluteModalLexicon

type AbsoluteModalPropLanguage = ModalPropLanguageWith AbsoluteModalLexicon

instance CopulaSchema AbsoluteModalPropLanguage

instance PrismIndexing AbsoluteModalPropLexicon World (World -> Bool) Bool
instance PrismIntIndex AbsoluteModalPropLexicon World
instance PrismCons AbsoluteModalPropLexicon World
instance PrismPolyadicSchematicFunction AbsoluteModalPropLexicon World World

type AbsoluteModalForm = AbsoluteModalPropLanguage (Form Bool)

type AbsoluteModalPreForm = AbsoluteModalPropLanguage (Form (World -> Bool))

----------------------------
--  6. Utility Functions  --
----------------------------
--convenience class

worldVar :: String -> WorldTheoryPropLanguage (Term World)
worldVar s = FX (Lx2 (Lx7 (Function (Var s) AZero)))
