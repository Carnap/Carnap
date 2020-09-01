{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.DefiniteDescription.Semantics
where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Languages.DefiniteDescription.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Semantics
import Control.Applicative

uniquelyDefines :: MonadicModel -> (Thing -> TruthValue) -> Maybe Thing
uniquelyDefines m f = case filter (unform . f) (domain m) of 
                          [x] -> Just x
                          _ -> Nothing

instance Modelable MonadicModel FregeanDescription where
        satisfies m (DefinDesc _) = \f -> case uniquelyDefines m f of
                                              Just x -> x
                                              Nothing -> Term 0

instance Modelable PolyadicModel FregeanDescription where
        satisfies m = satisfies (monadicPart m)
