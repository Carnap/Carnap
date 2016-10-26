{-#LANGUAGE ImpredicativeTypes, ScopedTypeVariables, FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Huet
        ( 
        )
    where

import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification



huetunify :: HigherOrder f
        => (forall a. f a -> Bool) --treat certain variables as constants
        -> [Equation f] --equations to be solved
        -> [Equation f] --accumulator for the substitution
        -> Either (UError f) [Equation f]

huetUnifySys :: (MonadVar f m, HigerOrder f) => (forall a. f a -> Bool) -> [Equation f] -> m [[Equation f]]

