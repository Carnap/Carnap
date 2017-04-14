{-#LANGUAGE FlexibleInstances, MultiParamTypeClasses, GADTs, TypeOperators, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable, StandaloneDeriving, DeriveGeneric #-}

module Carnap.Languages.PurePropositional.Syntax where

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

pattern PPred x arity  = Fx1 (Predicate x arity)
pattern PSPred x arity = Fx2 (Predicate x arity)
pattern PCon x arity   = Fx3 (Connective x arity)
pattern PSV n          = Fx4 (SubVar n)
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern PP n           = PPred (Prop n) AZero
pattern PPhi n         = PSPred (SProp n) AZero
pattern (:&:) x y      = PAnd :!$: x :!$: y
pattern (:||:) x y     = POr  :!$: x :!$: y
pattern (:->:) x y     = PIf  :!$: x :!$: y
pattern (:<->:) x y    = PIff :!$: x :!$: y
pattern PNeg x         = PNot :!$: x

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

instance Eq (PurePropLanguage a) where
        (==) = (=*)

instance UniformlyOrd PurePropLanguage where
        phi <=* psi = show phi <= show psi

data PropLangLabel = PropFormLabel
    deriving (Eq, Ord, Show)

instance Combineable PurePropLanguage PropLangLabel where
    getLabel _ = PropFormLabel

    getAlgo PropFormLabel = foUnifySys

    replaceChild (PNeg _)     pig _ = PNeg $ unEveryPig pig
    replaceChild (_ :&: x)    pig 0 = (unEveryPig pig) :&: x
    replaceChild (x :&: _)    pig 1 = x :&: (unEveryPig pig)
    replaceChild (_ :||: x)   pig 0 = (unEveryPig pig) :||: x
    replaceChild (x :||: _)   pig 1 = x :||: (unEveryPig pig)
    replaceChild (_ :->: x)   pig 0 = (unEveryPig pig) :->: x
    replaceChild (x :->: _)   pig 1 = x :->: (unEveryPig pig)
    replaceChild (_ :<->: x)  pig 0 = (unEveryPig pig) :<->: x
    replaceChild (x :<->: _)  pig 1 = x :<->: (unEveryPig pig)

--------------------------------------------------------
--Optics
--------------------------------------------------------

instance LangTypes1 PurePropLexicon Form Bool

predIndex :: Prism' (Predicate PureProp PurePropLanguage (Form Bool)) Int
predIndex = prism' (\n -> Predicate (Prop n) AZero) pm
    where pm :: Predicate PureProp idx (Form Bool) -> Maybe Int
          pm (Predicate (Prop n) AZero) = Just n
          pm _ = Nothing

propIndex :: Prism' PureForm Int
propIndex = link . predIndex
