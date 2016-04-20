module Combination () where

import Carnap.Core.Unification.Unification
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

--constraint that says that x must come before y
data Constraint f = (f a) :<: (f a)
data Clause f = [Constraint f]
data CNF f = [Clause f]

--only allow construction, not deconstruction (outside this module)
makeLabel :: TypeRep -> (Labeling f -> f a -> f a -> State [f a] [[Equation f]]) -> Label f
makeLabel = Label

class Combine f where
    getLabel :: f a -> Label f
    getConstraints :: CNF f
