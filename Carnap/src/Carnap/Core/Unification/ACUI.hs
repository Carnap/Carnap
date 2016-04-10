{-#LANGUAGE MultiParamTypeClasses, FlexibleContexts, PatternSynonyms #-}

module Carnap.Core.Unification.ACUI (
  acuiUnify, ACUI, unfoldTerm, refoldTerms,
  homogenous, solveHomoEq, inhomogenous,
  solveInHomoEq, pattern (:===:), toSatProblem,
  minimals
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

--determines weather a term is a non-empty constant
isConst a = not (isVar a || a == mempty)

--typeclass that contains everything we need to perform ACUI unfication
class (Show (f a), Eq (f a), Monoid (f a), FirstOrder f) => ACUI f a where
    --decompose into proper parts
    unfoldTerm :: f a -> [f a]

    refoldTerms :: [f a] -> f a
    refoldTerms [] = mempty
    refoldTerms [x] = x
    refoldTerms (x:xs) | x == mempty = refoldTerms xs
                       | otherwise   = x `mappend` refoldTerms xs

--a simiplair equation type we can work with here
data SimpleEquation a = a :==: a
    deriving(Eq, Ord, Show)

--export for testing
pattern (:===:) x y = x :==: y

--some helpers for minipulating equations
eqmap f (a :==: b) = f a :==: f b
eqfilter p (a :==: b) = (filter p a) :==: (filter p b)
eqadd (a :==: b) (a' :==: b') = (a ++ a') :==: (b ++ b')

--finds the index of a term
findIdx (l :==: r) x = let (Just idx) = findIndex (== x) (nub $ l ++ r) in idx + 1

--extracts the homogenous equation from the equation
homogenous eq = eqfilter isVar eq

--finds all inhomogenous equations that need to be solved
inhomogenous (l :==: r) = zip consts eqs
    where consts = filter isConst (nub $ l ++ r)
          eqs = map (\c -> eqfilter (\x -> isVar x || x == c) (l :==: r)) consts

--finds a term in an equation based on it's index
findTerm (l :==: r) i = nub (l ++ r) !! (i - 1)

--returns true if term maps to 'true' in the SAT problem
isTrue a = isConst a && a /= mempty
--returns true if a term maps to 'false' in a the SAT problem
isFalse a = a == mempty

--converts a SimpleEquation [f a] into a sat problem
toSatProblem eq@(a :==: b) | ltrue && rtrue = makeProb []
                           | ltrue     = makeProb [r]
                           | rtrue     = makeProb [l]
                           | lfalse && rfalse = makeProb []
                           | lfalse    = makeProb $ map (\x -> [negate x]) r
                           | rfalse    = makeProb $ map (\x -> [negate x]) l
                           | otherwise = makeProb $ (impl l r) ++ (impl r l)
    where impl ant con = map (\lit -> (negate lit):con) ant
          (l :==: r) = eqmap (map $ findIdx eq) eq
          ltrue = any isTrue a
          rtrue = any isTrue b
          lfalse = all isFalse a
          rfalse = all isFalse b
          vars = nub $ filter isVar (a ++ b)
          varsIdx = map (findIdx eq) vars
          makeProb = ListSat [] varsIdx

--returns true if the left side is strictly greater than the right side
dominates :: [Int] -> [Int] -> Bool
dominates l r = null $ (pos r) \\ (pos l)
    where pos = filter (> 0)

--finds all minimal non-trivial solutions being carful to never
--pattern match on a solution that we know is not minimal
minimals' :: [[Int]] -> [Int] -> Solutions -> [[Int]]
minimals' ss cur (Sat True) | all (<0) cur = ss
                            | otherwise    = cur:ss
minimals' ss cur (Sat False) = ss
minimals' ss cur (Sols i s1 s2) | any ((i:cur) `dominates`) mins = mins
                                | otherwise = minimals' mins (i:cur) s2
    where mins = minimals' ss ((negate i):cur) s1

--finds the trivial solution
trivialSol (Sols i s _) = map ((negate i) :) (trivialSol s)
trivialSol (Sat True)   = [[]]
trivialSol (Sat False)  = []

--finds all minimal solutions or the trivial solution if no nontrivial ones
--exist
minimals sols | null minsols = trivialSol sols
              | otherwise    = minsols
    where minsols = minimals' [] [] sols

--for now lets just find the solution to the homogenous setup
--we use it to get a fresh varible
pop :: State [a] a
pop = do
  (x:xs) <- get
  put xs
  return x

--simplifies a term by removing all empties
simplify e = refoldTerms (unfoldTerm e)

--uses vget to get the term being solved for and converts a solution
--into a substitution
conv vget eq sol = vget >>= \var -> return $ map (convVar var eq) sol
    where convVar var eq idx | idx > 0 = (findTerm eq idx) :==: var
                             | idx < 0 = (findTerm eq (abs idx)) :==: mempty

--adds substitutions togethor (in the way that adding solutions togethor)
--maps to under the homomorphism that takes solutions into substitutions
subadd :: (Eq m, Monoid m) => [SimpleEquation m] -> [SimpleEquation m] -> [SimpleEquation m]
subadd a b = like ++ unlike
    where like = [x :==: ((a' `mappend` b'))| (x :==: a') <- a, (y :==: b') <- b, x == y]
          unlike = filter (not . (`elem` (map eqleft like)) . eqleft) (a ++ b)
          eqleft (l :==: _) = l

--converts our internal equation represnetation to our external
toSub :: Show (f a) => [SimpleEquation (f a)] -> [Equation f]
toSub []              = []
toSub ((x :==: y):xs) = (x :=: y):(toSub xs)

--solves a homogenous equation
solveHomoEq :: ACUI f a => SimpleEquation [f a] -> State [f a] [SimpleEquation (f a)]
solveHomoEq eq = do
    let mins = minimals . search . toSatProblem $ eq
    minSols <- mapM (conv pop eq) mins
    let homosol = foldl subadd [] minSols
    return homosol

--solves an inhomogenous equation for a specific constant
solveInHomoEq :: ACUI f a => f a -> SimpleEquation [f a] -> State [f a] [[SimpleEquation (f a)]]
solveInHomoEq c eq = do
  let mins = minimals . search . toSatProblem $ eq
  minSols <- mapM (conv (return c) eq) mins
  return minSols

--some generic helpers for combining solutions
crossWith f xs ys = [f x y | x <- xs, y <- ys]
bigCrossWith f xs xss = foldr (crossWith f) xs xss

--finds all solutions to a = b
acuiUnify :: ACUI f a => f a -> f a -> State [f a] [[Equation f]]
acuiUnify a b = do
    let l = unfoldTerm a
    let r = unfoldTerm b
    let homo = homogenous (l :==: r)
    homosol <- solveHomoEq homo --solve the homogenous equation
    let inhomos = inhomogenous (l :==: r) --find all inhomogenous equations
    inhomosolss <- mapM (uncurry solveInHomoEq) inhomos --solve each one
    let sols = bigCrossWith subadd [homosol] inhomosolss --combine inhomo sols
    return $ map (toSub . map (eqmap simplify)) sols --simplify the solutions
