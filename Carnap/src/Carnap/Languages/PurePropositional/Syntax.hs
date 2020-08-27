{-#LANGUAGE FlexibleInstances, MultiParamTypeClasses, GADTs, TypeOperators, PatternSynonyms, RankNTypes, FlexibleContexts, StandaloneDeriving, DeriveGeneric #-}

module Carnap.Languages.PurePropositional.Syntax where

import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Types
import Carnap.Core.Data.Util (checkChildren)
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Util
import Carnap.Languages.Util.LanguageClasses
import Control.Lens.Plated (transform, children)
import Control.Applicative
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
        eval Iff = liftA2 (==) 
        eval If  = \(Form x) y -> if x then y else Form True
        eval Or  = \(Form x) y -> if x then Form True else y
        eval And = \(Form x) y -> if x then y else Form False
        --XXX: we avoid liftA2 here, to preserve laziness
        eval Not = fmap not

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

instance PrismPropLex PurePropLexicon Bool
instance PrismBooleanConnLex PurePropLexicon Bool
instance PrismGenericContext PurePropLexicon Bool Bool
instance PrismBooleanConst PurePropLexicon Bool
instance PrismSchematicProp PurePropLexicon Bool
instance PrismSubstitutionalVariable PurePropLexicon

instance CanonicalForm PureForm

instance Eq (PurePropLanguage a) where
        (==) = (=*)

instance UniformlyOrd PurePropLanguage where
        phi <=* psi = show phi <= show psi
