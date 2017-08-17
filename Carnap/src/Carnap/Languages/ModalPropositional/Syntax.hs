{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.ModalPropositional.Syntax
     where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (checkChildren)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Control.Lens.Plated (transform)
import Data.Typeable (Typeable)
import Data.Map.Lazy (Map, (!))
import Data.Monoid as M
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------
--  1. Data for Pure Propositional Modal Logic  --
--------------------------------------------------

--the semantic values in this language are intensions rather than boolean
--values

type World = Int

type ModalProp = IntProp (World -> Bool)

type Index = IntConst World

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

instance Modelable PropFrame ModalConn where
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

type ModalSchematicProp = SchematicIntProp (World -> Bool)

type ModalPropLanguageWith a = FixLang (CoreLexicon :|: a)
        
type CoreLexicon = Predicate ModalProp
                   :|: Predicate ModalSchematicProp
                   :|: Connective ModalConn
                   :|: Connective PropModality
                   :|: SubstitutionalVariable
                   :|: EndLang

instance BoundVars (CoreLexicon :|: a)

type ModalPropLanguage = ModalPropLanguageWith EndLang

type ModalForm = ModalPropLanguage (Form (World -> Bool))

instance CopulaSchema ModalPropLanguage

instance UniformlyEq (ModalPropLanguageWith a) => Eq (ModalPropLanguageWith a b) where
        (==) = (=*)

pattern MPred x arity  = FX (Lx1 (Lx1 (Predicate x arity)))
pattern MSPred x arity = FX (Lx1 (Lx2 (Predicate x arity)))
pattern MBCon x arity  = FX (Lx1 (Lx3 (Connective x arity)))
pattern MMCon x arity  = FX (Lx1 (Lx4 (Connective x arity)))
pattern MSV n          = FX (Lx1 (Lx5 (SubVar n)))
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

instance LangTypes1 (CoreLexicon :|: a) Form (World -> Bool)

instance BooleanLanguage (ModalPropLanguageWith a (Form (World -> Bool))) where
        land = (:&:)
        lneg = MNeg
        lor  = (:||:)
        lif  = (:->:)
        liff = (:<->:)

instance ModalLanguage (ModalPropLanguageWith a (Form (World -> Bool))) where
        nec = MNec
        pos = MPos

instance IndexedPropLanguage (ModalPropLanguageWith a (Form (World -> Bool))) where
        pn = MP

instance IndexedSchemePropLanguage (ModalPropLanguageWith a (Form (World -> Bool))) where
        phin = MPhi
