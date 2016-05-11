{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.PureFirstOrder.Syntax (
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (Plated)
import Control.Lens.Fold (anyOf)
import Control.Lens.Plated (cosmos, transform)
import Data.Typeable (Typeable)
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------------
--1. Data for Pure First Order Logic
--------------------------------------------------------

data PureMonadicPredicate a where
    MonPred :: Int -> PureMonadicPredicate Int

type PurePredicate = IntPred Bool Int

type PureConn = BooleanConn Bool

type PureSchematicPred = SchematicIntPred Bool Int

type PureConstant = IntConst Int

type PureQuant = StandardQuant Bool Int

--Polyadic First-Order Logic with Constant Symbols
type PureFirstOrderLexicon = (Predicate PurePredicate
                       :|: Predicate PureSchematicPred
                       :|: Connective PureConn
                       :|: Quantifiers PureQuant
                       :|: SubstitutionalVariable
                       :|: Function PureConstant
                       :|: EndLang)

type PureFirstOrderLanguage = FixLang PureFirstOrderLexicon

type PureFOLForm = PureFirstOrderLanguage (Form Bool)

instance CopulaSchema PureFirstOrderLanguage

pattern (:!!$:) :: (Typeable a, Typeable b) => PureFirstOrderLanguage (a -> b) -> PureFirstOrderLanguage a -> PureFirstOrderLanguage b
pattern (:!!$:) f y    = f :!$: y
pattern PPred x arity  = Fx1 (Predicate x arity)
pattern PSPred x arity = Fx2 (Predicate x arity)
pattern PCon x arity   = Fx3 (Connective x arity)
pattern PSV n          = Fx5 (SubVar n)
pattern PAnd           = PCon And ATwo
pattern POr            = PCon Or ATwo
pattern PIf            = PCon If ATwo
pattern PIff           = PCon Iff ATwo
pattern PNot           = PCon Not AOne
pattern PP n a1 a2     = PPred (Pred a1 n) a2
pattern PPhi n a1 a2   = PSPred (SPred a1 n) a2
pattern (:&:) x y      = PAnd :!!$: x :!!$: y
pattern (:||:) x y     = POr :!!$: x :!!$: y
pattern (:->:) x y     = PIf :!!$: x :!!$: y
pattern (:<->:) x y    = PIff :!!$: x :!!$: y
pattern PNeg x         = PNot :!!$: x

instance BooleanLanguage PureFOLForm where
        land = (:&:)
        lneg = PNeg
        lor  = (:||:)
        lif  = (:->:)
        liff = (:<->:)

instance PolyadicPredicateLanguage PureFirstOrderLanguage (Term Int) (Form Bool) 
        where
        ppn n a = PP n a a

pzero = AZero :: Arity (Term Int) (Form Bool) 'Zero (Form Bool)

instance CanonicalForm PureFOLForm
