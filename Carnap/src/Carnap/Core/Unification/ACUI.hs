module Carnap.Core.Unification.ACUI (
  isConst
) where

  --to solve ACUI unification with constants we need to be able to find
  --all minimal solutions to a SAT problem
import Carnap.Core.Unification.SAT
import Carnap.Core.Unification.Unification
import Data.Monoid
import Control.Lens
import Control.Lens.Plated
import Data.List

--anything you can perform ACU must be "multiset like" in a certian sense
--because of this we simple ask that you be able to convert it to a list of
--constants and varibles
isConst :: FirstOrder f => f a -> Bool
isConst a = not (isVar a) && null (decompose a a)

toProblem :: (Plated (f a), FirstOrder f) => f a -> [f a]
toProblem a = concatMap conv (children a)
    where conv x | isConst x = [x]
                 | isVar x   = [x]
                 | otherwise = toProblem a

--list out equations of the correct form that we need to solve
--in order to get our set of unifiers for

toEquations :: (Eq (f a), Plated (f a), FirstOrder f) => f a -> f a -> [([f a],[f a])]
toEquations a b = (varsA, varsB) : (map inhomo consts)
    where problemA = toProblem a
          problemB = toProblem b
          varsA = filter isVar problemA
          constsA = filter isConst problemA
          varsB = filter isVar problemB
          constsB = filter isConst problemB
          consts = nub (constsA ++ constsB)
          getConstA v = filter (==v) constsA
          getConstB v = filter (==v) constsB
          inhomo v = (varsA `mappend` getConstA v, varsB `mappend` getConstB v)
