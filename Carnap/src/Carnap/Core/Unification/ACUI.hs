{-#LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

module Carnap.Core.Unification.ACUI (
  acuiUnify,
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

class (Show (f a), Eq (f a), Monoid (f a), FirstOrder f) => ACUI f a where
    --decompose into proper parts
    unfoldTerm :: f a -> [f a]

    refoldTerms :: [f a] -> f a
    refoldTerms [] = mempty
    refoldTerms [x] = x
    refoldTerms (x:xs) | x == mempty = refoldTerms xs
                       | otherwise   = x `mappend` refoldTerms xs

--list out equations of the correct form that we need to solve
--in order to get our set of unifiers for
data SimpleEquation a = a :==: a
    deriving(Eq, Ord, Show)

eqmap f (a :==: b) = f a :==: f b
eqfilter p (a :==: b) = (filter p a) :==: (filter p b)
eqadd (a :==: b) (a' :==: b') = (a ++ a') :==: (b ++ b')

findIdx (l :==: r) x = let (Just idx) = findIndex (== x) (nub $ l ++ r) in idx + 1
homogenous eq = eqfilter isVar eq
inhomogenous (l :==: r) = zip consts eqs
    where consts = filter isConst (nub $ l ++ r)
          eqs = map (\c -> eqfilter (\x -> isVar x || x == c) (l :==: r)) consts
findTerm (l :==: r) i = nub (l ++ r) !! (i - 1)

isTrue a = isConst a && a /= mempty
isFalse a = a == mempty

--converts a SimpleEquation [f a] into a sat problem
toSatProblem eq@(a :==: b) | ltrue && rtrue = ListSat [] (nub $ l ++ r) []
                           | ltrue     = makeProblem [r]
                           | rtrue     = makeProblem [l]
                           | lfalse && rfalse = ListSat [] [] []
                           | lfalse    = makeProblem $ map (\x -> [negate x]) r
                           | rfalse    = makeProblem $ map (\x -> [negate x]) l
                           | otherwise = makeProblem $ (impl l r) ++ (impl r l)
    where impl ant con = map (\lit -> (negate lit):con) ant
          (l :==: r) = eqmap (map $ findIdx eq) eq
          ltrue = any isTrue a
          rtrue = any isTrue b
          lfalse = all isFalse a
          rfalse = all isFalse b

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
                               | otherwise = minimals mins (i:cur) s2
    where mins = minimals ss ((negate i):cur) s1

--for now lets just find the solution to the homogenous setup
pop :: State [a] a
pop = do
  (x:xs) <- get
  put xs
  return x

simplify e = refoldTerms (unfoldTerm e)

--pass the homogenous equation and a solution
--this will output a general solution
conv vget eq sol = vget >>= \var -> return $ map (convVar var eq) sol
    where convVar var eq idx | idx > 0 = (findTerm eq idx) :==: var
                             | idx < 0 = (findTerm eq (abs idx)) :==: mempty
--adds substitutions togethor
subadd :: (Eq m, Monoid m) => [SimpleEquation m] -> [SimpleEquation m] -> [SimpleEquation m]
subadd a b = like ++ unlike
    where like = [x :==: ((a' `mappend` b'))| (x :==: a') <- a, (y :==: b') <- b, x == y]
          unlike = filter (not . (`elem` (map eqleft like)) . eqleft) (a ++ b)
          eqleft (l :==: _) = l

toSub :: Show (f a) => [SimpleEquation (f a)] -> [Equation f]
toSub []              = []
toSub ((x :==: y):xs) = (x :=: y):(toSub xs)

solveHomoEq :: ACUI f a => SimpleEquation [f a] -> State [f a] [SimpleEquation (f a)]
solveHomoEq eq = do
    let mins = minimals [] [] . search . toSatProblem $ eq
    minSols <- mapM (conv pop eq) mins
    let homosol = foldl subadd [] minSols
    return $ map (eqmap simplify) homosol

--some code duplication here
--refactoring this code later will be a good idea
solveInHomoEq :: ACUI f a => f a -> SimpleEquation [f a] -> State [f a] [[SimpleEquation (f a)]]
solveInHomoEq c eq = do
  let mins = minimals [] [] . search . toSatProblem $ eq
  minSols <- mapM (conv (return c) eq) mins
  return $ (map . map . eqmap $ simplify) minSols

crossWith f xs ys = [f x y | x <- xs, y <- ys]
bigCrossWith f (xs:xss) = foldr (crossWith f) xs xss

acuiUnify :: ACUI f a => f a -> f a -> State [f a] [[Equation f]]
acuiUnify a b = do
    let l = unfoldTerm a
    let r = unfoldTerm b
    let homo = homogenous (l :==: r)
    homosol <- solveHomoEq homo --solve the homogenous equation
    let inhomos = inhomogenous (l :==: r) --find all inhomogenous equations
    inhomosolss <- mapM (uncurry solveInHomoEq) inhomos --solve each one
    let inhomosols = bigCrossWith subadd inhomosolss --combine inhomo sols
    return $ map (toSub . subadd homosol) inhomosols --lastly add homogenous sol
