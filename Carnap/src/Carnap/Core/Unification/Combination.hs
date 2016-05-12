module Combination (LabelPair(), Labeling, Label(), makeLabel, ) where

import Carnap.Core.Unification.Unification
import Carnap.Core.ModelChecking.ModelFinder
import Control.Monad.State
import Data.Typeable

data LabelPair f where
    LabelPair :: f a -> Label f -> LabelPair f

type Labeling f = [LabelPair f]

--each label needs a unique value associated with it and a unification algorithm
--we can get a unique value and ensure that it is unique by declaring a label
--type in a module and not exporting it. It is then garenteed that the value
--can not be reproduced so the label is garenteed unique since the Label
--constructor is also not exported
data Label f where
    Label :: TypeRep -> (Labeling f -> f a -> f a -> State [f a] [[Equation f]]) -> Label f

instance Eq (Label f) where
    (Label t _) == (Label t' _) = t == t'

--constraint that says that x must come before y

--only allow construction, not deconstruction (outside this module)
--this is to avoid the unessary error of constructing a label with the wrong
--type representation
makeLabel :: TypeRep -> (Labeling f -> f a -> f a -> State [f a] [[Equation f]]) -> Label f
makeLabel = Label

class Combine f where
    getLabel :: f a -> Label f
    getConstraints :: CNF f
