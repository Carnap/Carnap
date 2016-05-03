{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.ModalPropositional.Syntax 
     where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (Plated)
import Control.Lens.Fold (anyOf)
import Control.Lens.Plated (cosmos, transform)
import Data.Typeable (Typeable)
import Data.Map.Lazy (Map, (!))
import Data.Monoid
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
        satisfies f Box = lift1 $ \f x -> getAll $ mconcat (map (All . f) (ac x))
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


--XXX:Another case where "LangTypes1" would be nice to have
instance LangTypes ModalPropLexicon Form (World -> Bool) Term ()

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

checkChildren :: (Eq s, Plated s) => s -> s -> Bool
checkChildren phi psi = anyOf cosmos (== phi) psi

castToForm :: ModalPropLanguage a -> Maybe ModalForm
castToForm phi@(MNeg x)      = Just phi  
castToForm phi@(x :&: y)     = Just phi
castToForm phi@(x :||: y)    = Just phi
castToForm phi@(x :->: y)    = Just phi
castToForm phi@(x :<->: y)   = Just phi
castToForm phi@(MP _)        = Just phi
castToForm phi@(MPhi _)      = Just phi
castToForm phi@(MNec _)      = Just phi
castToForm phi@(MPos _)      = Just phi
castToForm _ = Nothing

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
    sameHead _ _ = False

    decompose (MNeg x) (MNeg y) = [x :=: y]
    decompose (MNec x) (MNec y) = [x :=: y]
    decompose (MPos x) (MPos y) = [x :=: y]
    decompose (x :&: y) (x' :&: y') = [x :=: x', y :=: y']
    decompose (x :||: y) (x' :||: y') = [x :=: x', y :=: y']
    decompose (x :->: y) (x' :->: y') = [x :=: x', y :=: y']
    decompose (x :<->: y) (x' :<->: y') = [x :=: x', y :=: y']
    decompose _ _ = []


    occurs phi psi = case (castToForm phi, castToForm psi) of
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
                case (castToForm v, castToForm phi, castToForm psi) of 
                     (Just v', Just phi', Just psi') -> 
                          transform (\x -> if x == v' then phi' else x) psi'
                     _ -> psi

    freshVars = map MSV [1..]
