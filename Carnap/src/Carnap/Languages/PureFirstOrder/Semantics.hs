{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.PureFirstOrder.Semantics
where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Languages.PurePropositional.Syntax (PureConst)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.GenericConstructors

type Thing = Term Int

type TruthValue = Form Bool

--------------------------------------
--  Pure Monadic First Order Logic  --
--------------------------------------

data MonadicModel = MonadicModel 
                  { domain :: [Thing]
                  , property :: Int -> Thing -> TruthValue
                  , name :: Int -> Thing
                  , proposition :: Int -> TruthValue
                  }

instance Modelable MonadicModel PureMonadicPredicate where
        satisfies m (MonPred n) = property m n

instance Modelable MonadicModel PureConstant where
        satisfies m (Constant n) = name m n

instance Modelable MonadicModel PureConst where
        satisfies m Verum = Form True
        satisfies m Falsum = Form False

instance Modelable MonadicModel PureQuant where
        satisfies m (All _) = (\f -> Form $ all (eval . f) (domain m))
        satisfies m (Some _) = (\f -> Form $ any (eval . f) (domain m))

instance Modelable MonadicModel PureVar where
        satisfies = error "it doesn't make sense to ask for the semantic value of an unbound variable"

instance Modelable MonadicModel (SchematicIntFunc Int Int) where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a function symbol)"

instance Modelable MonadicModel (PropositionalContext Bool) where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a propositional context)"

instance Modelable MonadicModel (IntProp Bool) where
        satisfies m (Prop n) = proposition m n
