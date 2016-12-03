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

--the semantic values in this language are intensions rather than boolean
--values

type World = Int

type ModalProp = IntProp (World -> Bool)

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

type ModalPropLexicon = (Predicate ModalProp
                   :|: Predicate ModalSchematicProp
                   :|: Connective ModalConn
                   :|: Connective PropModality
                   :|: SubstitutionalVariable
                   :|: EndLang)

instance BoundVars ModalPropLexicon

type ModalPropLanguage = FixLang ModalPropLexicon

instance CopulaSchema ModalPropLanguage

type ModalForm = ModalPropLanguage (Form (World -> Bool))

instance Eq ModalForm where
        (==) = (=*)

pattern MPred x arity  = Fx1 (Predicate x arity)
pattern MSPred x arity = Fx2 (Predicate x arity)
pattern MBCon x arity  = Fx3 (Connective x arity)
pattern MMCon x arity  = Fx4 (Connective x arity)
pattern MSV n          = Fx5 (SubVar n)
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

instance LangTypes1 ModalPropLexicon Form (World -> Bool)

instance BooleanLanguage ModalForm where
        land = (:&:)
        lneg = MNeg
        lor  = (:||:)
        lif  = (:->:)
        liff = (:<->:)

instance ModalLanguage ModalForm where
        nec = MNec
        pos = MPos

instance IndexedPropLanguage ModalForm where
        pn = MP

instance IndexedSchemePropLanguage ModalForm where
        phin = MPhi
