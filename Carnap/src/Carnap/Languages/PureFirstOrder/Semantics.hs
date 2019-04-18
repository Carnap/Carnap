{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.PureFirstOrder.Semantics
where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
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
        satisfies m (All _) = (\f -> pure $ all ((== Form True) . f) (domain m))
        satisfies m (Some _) = (\f -> pure $ any ((== Form True) . f) (domain m))

instance Modelable MonadicModel PureVar where
        satisfies = error "it doesn't make sense to ask for the semantic value of an unbound variable"

instance Modelable MonadicModel (SchematicIntFunc Int Int) where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a function symbol)"

instance Modelable MonadicModel (PropositionalContext Bool) where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a propositional context)"

instance Modelable MonadicModel (IntProp Bool) where
        satisfies m (Prop n) = proposition m n

----------------------------------
--  Polyadic First Order Logic  --
----------------------------------

data PolyadicModel = PolyadicModel 
                  { monadicPart :: MonadicModel
                  , relation :: forall ret. Arity Thing TruthValue ret -> Int -> ret
                  }

--Helper function for (safely) building a piece of a relation out of a list
--of lists of things. XXX - note that the order of the lists of things and
--of the arguments is reversed. So if [a,b,c] is in the list of lists, we
--have `toRelation l AThree b c a = True`
toRelation :: [[Thing]] -> Arity Thing TruthValue ret -> ret
toRelation list AZero = Form . not . null $ list
toRelation list (ASucc AZero) = \thing -> Form ([thing] `elem` list)
toRelation list (ASucc a) = \thing -> toRelation (map tail . filter (match thing) $ list) a
    where match thing (t:ts) = t == thing
          match thing _ = False

instance Modelable PolyadicModel PurePredicate where
        satisfies m (Pred a n) = relation m a n

instance Modelable PolyadicModel PureSchematicPred where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a predicate)"

instance Modelable PolyadicModel PureConstant where
        satisfies m c = satisfies (monadicPart m) c

instance Modelable PolyadicModel PureConst where
        satisfies m v = satisfies (monadicPart m) v

instance Modelable PolyadicModel PureQuant where
        satisfies m q = satisfies (monadicPart m) q

instance Modelable PolyadicModel PureVar where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel (SchematicIntFunc Int Int) where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel (PropositionalContext Bool) where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel (IntProp Bool) where
        satisfies m p = satisfies (monadicPart m) p
