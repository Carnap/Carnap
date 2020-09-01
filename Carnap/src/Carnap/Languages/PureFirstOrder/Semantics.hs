{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.PureFirstOrder.Semantics
where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Languages.PurePropositional.Syntax (PureConst,PureConn)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.GenericConstructors
import Data.Map as M (lookup,Map,filterWithKey,mapKeys)

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
        satisfies = const eval

instance Modelable MonadicModel PureEq where
        satisfies m TermEq = \t1 t2 -> Form (t1 == t2)

instance Modelable MonadicModel PureConn where
    satisfies = const eval

instance Modelable MonadicModel PureQuant where
        satisfies m (All _) = \f -> Form (all (unform . f) (domain m))
        satisfies m (Some _) = \f -> Form (any (unform . f) (domain m))

instance Modelable MonadicModel PureVar where
        satisfies = error "it doesn't make sense to ask for the semantic value of an unbound variable"

instance Modelable MonadicModel (SchematicIntFunc Int Int) where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a function symbol)"

instance Modelable MonadicModel (PropositionalContext Bool) where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a propositional context)"

instance Modelable MonadicModel (QuantifiedContext Bool Int lang) where
        satisfies = error "it doesn't make sense to ask for the semantic value of a schematic variable (in this case a quantified context)"

instance Modelable MonadicModel (IntProp Bool) where
        satisfies m (Prop n) = proposition m n

----------------------------------
--  Polyadic First Order Logic  --
----------------------------------

data PolyadicModel = PolyadicModel 
                  { monadicPart :: MonadicModel
                  , relation :: forall ret. Arity Thing TruthValue ret -> Int -> ret
                  , function :: forall ret. Arity Thing Thing ret -> Int -> ret
                  }

--Helper function for (safely) building a piece of a relation out of a list
--of lists of things. 
toRelation :: [[Thing]] -> Arity Thing TruthValue ret -> ret
toRelation list AZero = Form . not . null $ list
toRelation list (AOne) = \t -> Form ([t] `elem` list)
toRelation list (ATwo) = \t t' -> Form ([t,t'] `elem` list)
toRelation list (AThree) = \t t' t''-> Form ([t,t',t''] `elem` list)
toRelation list (ASucc a) = \thing -> toRelation (map tail . filter (match thing) $ list) a
    where match thing (t:ts) = t == thing
          match thing _ = False

toFunction :: Map [Thing] Thing -> Arity Thing Thing ret -> ret
toFunction theMap AZero = case M.lookup [] theMap of Just t -> t; _ -> Term 0
toFunction theMap (ASucc AZero) = \thing -> case M.lookup [thing] theMap of Just t -> t; _ -> Term 0
toFunction theMap (ASucc a) = \thing -> toFunction (mapKeys tail . filterWithKey (match thing) $ theMap) a
    where match thing (t:ts) _ = t == thing
          match thing _ _ = False

instance Modelable PolyadicModel PurePredicate where
        satisfies m (Pred a n) = relation m a n

instance Modelable PolyadicModel PureFunction where
        satisfies m (Func a n) = function m a n

instance Modelable PolyadicModel PureConstant where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel PureConst where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel PureEq where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel PureConn where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel PureQuant where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel PureVar where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel (SchematicIntFunc Int Int) where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel (PropositionalContext Bool) where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel (QuantifiedContext Bool Int lang) where
        satisfies m = satisfies (monadicPart m)

instance Modelable PolyadicModel (IntProp Bool) where
        satisfies m = satisfies (monadicPart m)
