{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Languages.PurePropositional.Syntax where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (Plated)
import Control.Lens.Fold (anyOf)
import Control.Lens.Plated (cosmos, transform)
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConnectives

type PureProp = IntProp Bool

instance Evaluable PureProp where
        eval (Prop n) = Form $ even n

instance Modelable (Int -> Bool) PureProp where
        satisfies f (Prop n) = Form $ f n

type PureConn = BooleanConn Bool

instance Evaluable PureConn where
        eval Iff = lift2  (==)
        eval If = lift2 $ \x y -> (not x || y)
        eval Or = lift2  (||)
        eval And = lift2 (&&)
        eval Not = lift1 not

instance Modelable (Int -> Bool) PureConn where
    satisfies = const eval

type PureSchematicProp = SchematicIntProp Bool

type PurePropLexicon = (Predicate PureProp
                   :|: Predicate PureSchematicProp
                   :|: Connective PureConn
                   :|: SubstitutionalVariable
                   :|: EndLang)

type PurePropLanguage = FixLang PurePropLexicon

type PureForm = PurePropLanguage (Form Bool)

pattern (:!!$:) :: (Typeable a, Typeable b) => PurePropLanguage (a -> b) -> PurePropLanguage a -> PurePropLanguage b
pattern (:!!$:) f y    = f :!$: y
pattern PPred x arity  = Fx1 (Predicate x arity)
pattern PSPred x arity = Fx2 (Predicate x arity)
pattern PCon x arity   = Fx3 (Connective x arity)
pattern PSV n           = Fx4 (SubVar n)
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern PP n            = PPred (Prop n) AZero
pattern PPhi n          = PSPred (SProp n) AZero
pattern (:&:) x y      = PAnd :!!$: x :!!$: y
pattern (:||:) x y     = POr :!!$: x :!!$: y
pattern (:->:) x y     = PIf :!!$: x :!!$: y
pattern (:<->:) x y    = PIff :!!$: x :!!$: y
pattern PNeg x          = PNot :!!$: x

instance CopulaSchema PurePropLanguage where
    appSchema x y e = schematize x (show y : e)
    lamSchema = error "how did you even do this?"
    liftSchema = error "should not print a lifted value"

instance BoundVars PurePropLexicon where

    getBoundVar _ = undefined

    subBoundVar _ _ phi = phi

--XXX:This is a little awkward. Ideally, maybe have LangTypes1, LangTypes2,
--LangTypes3...
instance LangTypes PurePropLexicon Form Bool Term ()

instance RelabelVars PurePropLexicon Form Bool where
        subBinder _ _ = Nothing

instance CanonicalForm PureForm where
        canonical = id

instance BooleanLanguage PureForm where
        land = (:&:)
        lneg = PNeg
        lor  = (:||:)
        lif  = (:->:)
        liff = (:<->:)

instance IndexedPropLanguage PureForm where
        pn = PP

checkChildren phi psi = anyOf cosmos (== phi) psi

castToForm :: PurePropLanguage a -> Maybe PureForm
castToForm phi@(PNeg x)     = Just phi  
castToForm phi@(x :&: y)    = Just phi
castToForm phi@(x :||: y)   = Just phi
castToForm phi@(x :->: y)   = Just phi
castToForm phi@(x :<->: y)  = Just phi
castToForm phi@(PP _)        = Just phi
castToForm phi@(PPhi _)      = Just phi
castToForm _ = Nothing

instance FirstOrder PurePropLanguage where
        
    isVar (PPhi _) = True
    isVar _        = False

    sameHead (PNeg _) (PNeg _) = True
    sameHead (_ :&: _) (_ :&: _) = True
    sameHead (_ :||: _) (_ :||: _) = True
    sameHead (_ :->: _) (_ :->: _) = True
    sameHead (_ :<->: _) (_ :<->: _) = True
    sameHead _ _ = False

    decompose (PNeg x) (PNeg y) = [x :=: y]
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
            (PNeg x)     -> byCast a b c
            (x :&: y)    -> byCast a b c 
            (x :||: y)   -> byCast a b c
            (x :->: y)   -> byCast a b c
            (x :<->: y)  -> byCast a b c
            (PP _)       -> byCast a b c
            (PPhi _)     -> byCast a b c
            _ -> c
        where 
            byCast v phi psi =
                case (castToForm v, castToForm phi, castToForm psi) of 
                     (Just v', Just phi', Just psi') -> 
                          transform (\x -> if x == v' then phi' else x) psi'
                     _ -> psi

    freshVars = map PSV [1..]



