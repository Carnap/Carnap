{-#LANGUAGE FlexibleInstances, MultiParamTypeClasses, GADTs, TypeOperators, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable, StandaloneDeriving, DeriveGeneric #-}

module Carnap.Languages.PurePropositional.Syntax where

import Carnap.Core.Data.Optics
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.Util (checkChildren)
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Util
import Carnap.Languages.Util.LanguageClasses
import Control.Lens.Plated (transform, children)
import Control.Lens.Prism
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConstructors

type PureProp = IntProp Bool

instance Evaluable PureProp where
        eval (Prop n) = Form $ even n

instance Modelable (Int -> Bool) PureProp where
        satisfies f (Prop n) = Form $ f n

type PureConn = BooleanConn Bool

instance Evaluable PureConn where
        eval Iff = lift2  (==)
        eval If  = lift2 $ \x y -> (not x || y)
        eval Or  = lift2  (||)
        eval And = lift2 (&&)
        eval Not = lift1 not

instance Modelable (Int -> Bool) PureConn where
    satisfies = const eval

type PureConst = BooleanConst Bool

instance Evaluable PureConst where
        eval Verum = Form True
        eval Falsum = Form False

instance Modelable (Int -> Bool) PureConst where
    satisfies = const eval

type PureSchematicProp = SchematicIntProp Bool

type PurePropositionalContext = PropositionalContext Bool

instance Evaluable PurePropositionalContext where
        eval _ = error "don't evaluate schemata!"

instance Modelable (Int -> Bool) PurePropositionalContext where
    satisfies = const eval

type PurePropLexicon = Predicate PureProp
                   :|: Predicate PureSchematicProp
                   :|: Connective PureConn
                   :|: SubstitutionalVariable
                   :|: Connective PurePropositionalContext
                   :|: Connective PureConst
                   :|: EndLang

instance BoundVars PurePropLexicon

type PurePropLanguage = FixLang PurePropLexicon

instance CopulaSchema PurePropLanguage

type PureForm = PurePropLanguage (Form Bool)

pattern PCon x arity   = Fx3 (Connective x arity)
pattern PSV n          = Fx4 (SubVar n)
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern (:&:) x y      = PAnd :!$: x :!$: y
pattern (:||:) x y     = POr  :!$: x :!$: y
pattern (:->:) x y     = PIf  :!$: x :!$: y
pattern (:<->:) x y    = PIff :!$: x :!$: y
pattern PNeg x         = PNot :!$: x

instance PrismPropLex PurePropLexicon Bool
instance PrismBooleanConnLex PurePropLexicon Bool
instance PrismPropositionalContext PurePropLexicon Bool
instance PrismBooleanConst PurePropLexicon Bool
instance PrismSchematicProp PurePropLexicon Bool
instance PrismSubstitutionalVariable PurePropLexicon

instance CanonicalForm PureForm

instance Eq (PurePropLanguage a) where
        (==) = (=*)

instance UniformlyOrd PurePropLanguage where
        phi <=* psi = show phi <= show psi

data PropLangLabel = PropFormLabel
    deriving (Eq, Ord, Show)

-- instance Combineable PurePropLanguage PropLangLabel where
--     getLabel _ = PropFormLabel

--     getAlgo PropFormLabel = foUnifySys

--     replaceChild (PNeg _)     pig _ = PNeg $ unEveryPig pig
--     replaceChild (_ :&: x)    pig 0 = (unEveryPig pig) :&: x
--     replaceChild (x :&: _)    pig 1 = x :&: (unEveryPig pig)
--     replaceChild (_ :||: x)   pig 0 = (unEveryPig pig) :||: x
--     replaceChild (x :||: _)   pig 1 = x :||: (unEveryPig pig)
--     replaceChild (_ :->: x)   pig 0 = (unEveryPig pig) :->: x
--     replaceChild (x :->: _)   pig 1 = x :->: (unEveryPig pig)
--     replaceChild (_ :<->: x)  pig 0 = (unEveryPig pig) :<->: x
--     replaceChild (x :<->: _)  pig 1 = x :<->: (unEveryPig pig)
