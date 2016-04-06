module Carnap.Core.Unification.ACUI (
  isConst, acuiUnify
) where

  --to solve ACUI unification with constants we need to be able to find
  --all minimal solutions to a SAT problem
import Carnap.Core.Unification.SAT
import Carnap.Core.Unification.Unification
import Data.Monoid
import Control.Lens
import Control.Monad.State
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

refoldTerms :: Monoid m => [m] -> m
refoldTerms = mconcat

--list out equations of the correct form that we need to solve
--in order to get our set of unifiers for
data SimpleEquation a = a :==: a

eqmap f (a :==: b) = f a :==: f b
eqfilter p (a :==: b) = (filter p a) :==: (filter p b)
eqadd (a :==: b) (a' :==: b') = (a ++ a') :==: (b ++ b')

findIdx (l :==: r) x = let (Just idx) = findIndex (== x) (nub $ l ++ r) in idx
homogenous eq = eqfilter isVar eq
inhomogenous (l :==: r) = map (\c -> eqfilter (\x -> isVar x || x == c) (l :==: r))
    where consts = filter (not . isVar) (l ++ r)
findTerm (l :==: r) i = nub (l ++ r) !! i

--converts a homogenous problem to a non-homogenous one
toSatProblem :: SimpleEquation [Int] -> [[Int]]
toSatProblem (l :==: r) = (impl l r) ++ (impl r l)
    where impl ant con = map (\lit -> (negate lit):con) ant

dominates :: [Int] -> [Int] -> Bool
dominates l r = null $ (pos r) \\ (pos l)
    where pos = filter (> 0)

--find all minimal solutions being carful to never
--pattern match on a solution that we know is not minimal
minimals :: [[Int]] -> [Int] -> Solutions -> [[Int]]
minimals ss cur (Sat True) | all (<0) cur = ss
                           | otherwise    = cur:ss
minimals ss cur (Sat False) = ss
minimals ss cur (Sols i s1 s2) | any ((i:cur) `dominates`) mins = mins
                               | otherwise = mins ++ minimals mins (i:cur) s2
    where mins = minimals ss ((negate i):cur) s1

--for now lets just find the solution to the homogenous setup
pop :: State [a] a
pop = do
  (x:xs) <- get
  put xs
  return x
ezip = zipWith (:==:)
--pass the homogenous equation and a solution
--this will output a general solution
conv (l :==: r) sol = do
    var <- pop
    let sub = ezip (l ++ r) (map (mconcat . flip replicate var) sol)
    return sub

--adds substitutions togethor
subadd :: (Eq m, Monoid m) => [SimpleEquation m] -> [SimpleEquation m] -> [SimpleEquation m]
subadd a b = like ++ unlike
    where like = [x :==: (a' `mappend` b')| (x :==: a') <- a, (y :==: b') <- a, x == y]
          unlike = filter (not . (`elem` (map eqleft like)) . eqleft) a
          eqleft (l :==: _) = l

toSub :: Show (f a) => [SimpleEquation (f a)] -> [Equation f]
toSub []              = []
toSub ((x :==: y):xs) = (x :=: y):(toSub xs)

acuiUnify :: Show (f a) => (Eq (f a), Monoid (f a), Plated (f a), FirstOrder f)
          => f a -> f a -> State [f a] [Equation f]
acuiUnify a b = do
    let l = unfoldTerm a
    let r = unfoldTerm b
    let homo = homogenous (l :==: r)
    let homo' = eqmap (map $ findIdx homo) $ homo
    let mins = minimals [] [] . search . makeProblem . toSatProblem $ homo'
    minSols <- mapM (conv homo) mins
    return $ toSub (foldl subadd [] minSols)
