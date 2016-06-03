{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.ModalPropositional.Syntax 
     where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (Syncast(..), checkChildren)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Control.Lens.Plated (Plated, cosmos, transform)
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
        satisfies f Box = lift1 $ \f x -> getAll $ mconcat (map (M.All . f) (ac x))
            where ac x = accessibility f ! x
        satisfies f Diamond = lift1 $ \f x -> getAny $ mconcat (map (Any . f) (ac x))
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

instance CanonicalForm ModalForm

pattern (:!!$:) :: (Typeable a, Typeable b) => ModalPropLanguage (a -> b) -> ModalPropLanguage a -> ModalPropLanguage b
pattern (:!!$:) f y    = f :!$: y
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
pattern (:&:) x y      = MAnd :!!$: x :!!$: y
pattern (:||:) x y     = MOr :!!$: x :!!$: y
pattern (:->:) x y     = MIf :!!$: x :!!$: y
pattern (:<->:) x y    = MIff :!!$: x :!!$: y
pattern MNeg x         = MNot :!!$: x
pattern MNec x         = MBox :!!$: x
pattern MPos x         = MDiamond :!!$: x

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

instance Syncast ModalPropLanguage (Form (World -> Bool)) where
    cast phi@(MNeg x)      = Just phi  
    cast phi@(x :&: y)     = Just phi
    cast phi@(x :||: y)    = Just phi
    cast phi@(x :->: y)    = Just phi
    cast phi@(x :<->: y)   = Just phi
    cast phi@(MP _)        = Just phi
    cast phi@(MPhi _)      = Just phi
    cast phi@(MNec _)      = Just phi
    cast phi@(MPos _)      = Just phi
    cast _ = Nothing

instance FirstOrder ModalPropLanguage where
        
    isVar (MPhi _) = True
    isVar _        = False

    sameHead (MNeg _) (MNeg _) = True
    sameHead (_ :&: _) (_ :&: _) = True
    sameHead (_ :||: _) (_ :||: _) = True
    sameHead (_ :->: _) (_ :->: _) = True
    sameHead (_ :<->: _) (_ :<->: _) = True
    sameHead (MNec _) (MNec _) = True
    sameHead (MPos _) (MPos _) = True
    sameHead (MP n) (MP m) = n == m
    sameHead _ _ = False

    decompose (MNeg x) (MNeg y) = [x :=: y]
    decompose (MNec x) (MNec y) = [x :=: y]
    decompose (MPos x) (MPos y) = [x :=: y]
    decompose (x :&: y) (x' :&: y') = [x :=: x', y :=: y']
    decompose (x :||: y) (x' :||: y') = [x :=: x', y :=: y']
    decompose (x :->: y) (x' :->: y') = [x :=: x', y :=: y']
    decompose (x :<->: y) (x' :<->: y') = [x :=: x', y :=: y']
    decompose _ _ = []

    occurs phi psi = case (cast phi :: Maybe ModalForm, cast psi :: Maybe ModalForm) of
                                 (Just f, Just f') -> checkChildren f f'
                                 _ -> False

    subst a b c = 
          case c of 
            (MNeg _)     -> byCast a b c
            (_ :&: _)    -> byCast a b c 
            (_ :||: _)   -> byCast a b c
            (_ :->: _)   -> byCast a b c
            (_ :<->: _)  -> byCast a b c
            (MP _)       -> byCast a b c
            (MPhi _)     -> byCast a b c
            (MNec _)     -> byCast a b c
            (MPos _)     -> byCast a b c
            _            -> c
        where 
            byCast v phi psi =
                case (cast v :: Maybe ModalForm, cast phi :: Maybe ModalForm, cast psi :: Maybe ModalForm) of 
                     (Just v', Just phi', Just psi') -> 
                          transform (\x -> if x == v' then phi' else x) psi'
                     _ -> psi

    freshVars = map MSV [1..]
