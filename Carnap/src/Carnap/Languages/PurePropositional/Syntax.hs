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

instance BoundVars PurePropLexicon

type PurePropLanguage = FixLang PurePropLexicon

instance CopulaSchema PurePropLanguage

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

instance BooleanLanguage PureForm where
        land = (:&:)
        lneg = PNeg
        lor  = (:||:)
        lif  = (:->:)
        liff = (:<->:)

instance IndexedPropLanguage PureForm where
        pn = PP

instance IndexedSchemePropLanguage PureForm where
        phin = PPhi

instance CanonicalForm PureForm

instance LangTypes1 PurePropLexicon Form Bool

checkChildren :: (Eq s, Plated s) => s -> s -> Bool
checkChildren phi psi = anyOf cosmos (== phi) psi

instance Syncast PurePropLanguage (Form Bool) where
    cast phi@(PNeg x)      = Just phi  
    cast phi@(x :&: y)     = Just phi
    cast phi@(x :||: y)    = Just phi
    cast phi@(x :->: y)    = Just phi
    cast phi@(x :<->: y)   = Just phi
    cast phi@(PP _)        = Just phi
    cast phi@(PPhi _)      = Just phi
    cast _ = Nothing

instance FirstOrder PurePropLanguage where
        
    isVar (PPhi _) = True
    isVar _        = False

    sameHead (PNeg _) (PNeg _) = True
    sameHead (_ :&: _) (_ :&: _) = True
    sameHead (_ :||: _) (_ :||: _) = True
    sameHead (_ :->: _) (_ :->: _) = True
    sameHead (_ :<->: _) (_ :<->: _) = True
    sameHead (PP n) (PP m) = n == m
    sameHead _ _ = False

    decompose (PNeg x) (PNeg y) = [x :=: y]
    decompose (x :&: y) (x' :&: y') = [x :=: x', y :=: y']
    decompose (x :||: y) (x' :||: y') = [x :=: x', y :=: y']
    decompose (x :->: y) (x' :->: y') = [x :=: x', y :=: y']
    decompose (x :<->: y) (x' :<->: y') = [x :=: x', y :=: y']
    decompose _ _ = []

    occurs phi psi = case (cast phi :: Maybe PureForm, cast psi :: Maybe PureForm)
                            of (Just f, Just f') -> checkChildren f f'
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
                case (cast v :: Maybe PureForm, cast phi :: Maybe PureForm, cast psi :: Maybe PureForm) of 
                     (Just v', Just phi', Just psi') -> 
                          transform (\x -> if x == v' then phi' else x) psi'
                     _ -> psi

    freshVars = map PSV [1..]
