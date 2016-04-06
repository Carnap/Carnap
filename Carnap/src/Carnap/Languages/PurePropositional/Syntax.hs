{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Languages.PurePropositional.Syntax where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Control.Lens (Plated)
import Control.Lens.Fold (anyOf)
import Control.Lens.Plated (cosmos, transform)
import Data.Typeable (Typeable)

data PureProp a where
        Prop :: Int -> PureProp (Form Bool)

instance Schematizable PureProp where
        schematize (Prop n)   _       = "P_" ++ show n

instance Evaluable PureProp where
        eval (Prop n) = Form $ even n

instance Modelable (Int -> Bool) PureProp where
        satisfies f (Prop n) = Form $ f n

data PureConn a where
        And :: PureConn (Form Bool -> Form Bool -> Form Bool)
        Or :: PureConn (Form Bool -> Form Bool -> Form Bool)
        If :: PureConn (Form Bool -> Form Bool -> Form Bool)
        Iff :: PureConn (Form Bool -> Form Bool -> Form Bool)
        Not :: PureConn (Form Bool -> Form Bool)


instance Schematizable PureConn where
        schematize Iff = \(x:y:_) -> "(" ++ x ++ " ↔ " ++ y ++ ")"
        schematize If  = \(x:y:_) -> "(" ++ x ++ " → " ++ y ++ ")"
        schematize Or = \(x:y:_) -> "(" ++ x ++ " ∨ " ++ y ++ ")"
        schematize And = \(x:y:_) -> "(" ++ x ++ " ∧ " ++ y ++ ")"
        schematize Not = \(x:_) -> "¬" ++ x

instance Evaluable PureConn where
        eval Iff = lift2  (==)
        eval If = lift2 $ \x y -> (not x || y)
        eval Or = lift2  (||)
        eval And = lift2 (&&)
        eval Not = lift1 not

instance Modelable (Int -> Bool) PureConn where
    satisfies _ x = eval x

data SchematicProp a where
        SProp :: Int -> SchematicProp (Form Bool)

instance Schematizable SchematicProp where
        schematize (SProp n)   _       = "φ_" ++ show n

--XXX:All Schematic Propositions are false. A better solution might make
--a schematic language take semantic values in a Maybe monad
instance Evaluable SchematicProp where
        eval (SProp _) = Form False

instance Modelable (Int -> Bool) SchematicProp where
        satisfies _ (SProp _) = Form False

type PurePropLexicon = (Predicate PureProp
                   :|: Predicate SchematicProp
                   :|: Connective PureConn
                   :|: EndLang)

type PurePropLanguage = FixLang PurePropLexicon

type PureForm = PurePropLanguage (Form Bool)

pattern (:!!$:) :: (Typeable a, Typeable b) => PurePropLanguage (a -> b) -> PurePropLanguage a -> PurePropLanguage b
pattern (:!!$:) f y    = f :!$: y
pattern PPred x arity  = Fx1 (Predicate x arity)
pattern PSPred x arity = Fx2 (Predicate x arity)
pattern PCon x arity   = Fx3 (Connective x arity)
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern P n            = PPred (Prop n) AZero
pattern Phi n          = PSPred (SProp n) AZero
pattern PConj x y       = PAnd :!!$: x :!!$: y
pattern (:&:) x y      = PAnd :!!$: x :!!$: y
pattern (:||:) x y     = POr :!!$: x :!!$: y
pattern (:->:) x y     = PIf :!!$: x :!!$: y
pattern (:<->:) x y    = PIff :!!$: x :!!$: y
pattern Neg x          = PNot :!!$: x

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

checkChildren phi psi = anyOf cosmos (== phi) psi

castToForm :: PurePropLanguage a -> Maybe PureForm
castToForm phi@(Neg x)     = Just phi  
castToForm phi@(x :&: y)   = Just phi
castToForm phi@(x :||: y)  = Just phi
castToForm phi@(x :->: y)  = Just phi
castToForm phi@(x :<->: y) = Just phi
castToForm phi@(P _)       = Just phi
castToForm phi@(Phi _)     = Just phi
castToForm _ = Nothing

instance FirstOrder PurePropLanguage where
        
    isVar (Phi _) = True
    isVar _       = False

    sameHead (Neg _) (Neg _) = True
    sameHead (_ :&: _) (_ :&: _) = True
    sameHead (_ :||: _) (_ :||: _) = True
    sameHead (_ :->: _) (_ :->: _) = True
    sameHead (_ :<->: _) (_ :<->: _) = True
    sameHead _ _ = False

    decompose (Neg x) (Neg y) = [x :=: y]
    decompose (x :&: y) (x' :&: y') = [x :=: x', y :=: y']
    decompose (x :||: y) (x' :||: y') = [x :=: x', y :=: y']
    decompose (x :->: y) (x' :->: y') = [x :=: x', y :=: y']
    decompose (x :<->: y) (x' :<->: y') = [x :=: x', y :=: y']
    decompose _ _ = []

    occurs phi (Neg x) = checkChildren phi x
    occurs phi (x :&: y) = checkChildren phi x || checkChildren phi y
    occurs phi (x :||: y) = checkChildren phi x || checkChildren phi y
    occurs phi (x :->: y) = checkChildren phi x || checkChildren phi y
    occurs phi (x :<->: y) = checkChildren phi x || checkChildren phi y
    occurs phi psi@(P _) = phi == psi
    occurs phi psi@(Phi _) = phi == psi
    occurs _ _ = False

    subst a b c = 
          case c of 
            (Neg x)     -> byCast a b c
            (x :&: y)   -> byCast a b c 
            (x :||: y)  -> byCast a b c
            (x :->: y)  -> byCast a b c
            (x :<->: y) -> byCast a b c
            (P _)       -> byCast a b c
            (Phi _)     -> byCast a b c
            _ -> c
        where 
            byCast v phi psi =
                case (castToForm v, castToForm phi, castToForm psi) of 
                     (Just v', Just phi', Just psi') -> 
                          transform (\x -> if x == v' then phi' else x) psi'
                     _ -> psi
