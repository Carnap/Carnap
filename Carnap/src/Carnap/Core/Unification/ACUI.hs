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
import Data.Function

--anything you can perform ACU must be "multiset like" in a certian sense
--because of this we simple ask that you be able to convert it to a list of
--constants and varibles
isConst :: FirstOrder f => f a -> Bool
isConst a = not (isVar a) && null (decompose a a)

unfoldTerm :: (Plated (f a), FirstOrder f) => f a -> [f a]
unfoldTerm a = concatMap conv (children a)
    where conv x | isConst x = [x]
                 | isVar x   = [x]
                 | otherwise = unfoldTerm a

--list out equations of the correct form that we need to solve
--in order to get our set of unifiers for
data SimpleEquation a = a :==: a

eqmap f (a :==: b) = f a :==: f b
eqfilter p (a :==: b) = (filter p a) :==: (filter p b)

--toEquations :: [f a] -> [f a] -> (SimpleEquation [f a], [SimpleEquation [f a]])
toEquations l r = (homo, inhomos)
    where eq = l :==: r
          homo = eqfilter isVar eq
          consts = filter (not . isVar) (l ++ r)
          inhomos = map (\c -> eqfilter (\x -> isVar x || x == c) eq) consts
          --vars = filter isVar 
          --parts = nub (vars ++ consts)
          --findi x = (find . ((==) `on` fst)) x (zip parts [1..]) >>= return . snd
