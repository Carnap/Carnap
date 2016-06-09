{-#LANGUAGE MultiParamTypeClasses, FlexibleContexts, PatternSynonyms #-}

module Combination (LabelPair(), Labeling, Label(), makeLabel) where

import Carnap.Core.Unification.Unification
import Carnap.Core.ModelChecking.ModelFinder
import Control.Monad.State
import Data.Typeable

data LabelPair f where
    LabelPair :: Combineable f label => f a -> label -> LabelPair f

type Labeling f = [LabelPair f]

type UniFunction f = Labeling f -> f a -> f a -> State [f a] [[Equation f]]

class (FirstOrder f, Eq label) => Combineable f label | f -> label where
    getLabel :: f a -> label
    getAlgo :: label -> UniFunction f
    replaceArgs ::

splitEqs :: Combineable f label => Equation f -> [(label, Equation f)]
splitEqs eq@(a :=: b)
    | getLabel a == getLabel b && sameHead a b = decompose eq >>= splitEqs --head dosn't matter
    | getLabel a == getLabel b                 = undefined --head matters a
    | otherwise                                = undefined --
