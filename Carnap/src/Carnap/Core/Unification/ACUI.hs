{-#LANGUAGE ImpredicativeTypes, MultiParamTypeClasses, FlexibleContexts, PatternSynonyms #-}

module Carnap.Core.Unification.ACUI (
  acuiUnify, ACUI, unfoldTerm, refoldTerms
) where

  --to solve ACUI unification with constants we need to be able to find
  --all minimal solutions to a SAT problem
import Carnap.Core.ModelChecking.SAT
import Carnap.Core.Unification.Unification
import Carnap.Core.Util
import Data.Monoid
import Data.Typeable
import Control.Lens
import Control.Monad.State
import Control.Lens.Plated
import Data.List
import Data.Function

--determines weather a term is a non-empty constant
isConst a = not (isVar a || a == mempty)

--typeclass that contains everything we need to perform ACUI unfication
class (Typeable a, Eq (f a), Monoid (f a), FirstOrder f) => ACUI f a where
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

--extracts the homogenous equation from the equation
homogenous eq = eqfilter isVar eq
--finds all inhomogenous equations that need to be solved
inhomogenous (l :==: r) = zip consts eqs
    where consts = filter isConst (nub $ l ++ r)
          eqs = map (\c -> eqfilter (\x -> isVar x || x == c) (l :==: r)) consts

--returns true if term maps to 'true' in the SAT problem
isTrue a = isConst a && a /= mempty
--returns true if a term maps to 'false' in a the SAT problem
isFalse a = a == mempty


--converts a SimpleEquation [f a] into a sat problem
toSatProblem :: (ACUI f a) => SimpleEquation [f a] -> ListSat (f a)
toSatProblem eq@(a :==: b) | ltrue && rtrue = makeProb []
                           | ltrue     = makeProb [map LPos b]
                           | rtrue     = makeProb [map LPos a]
                           | lfalse && rfalse = makeProb []
                           | lfalse    = makeProb $ map (\x -> [LNeg x]) b
                           | rfalse    = makeProb $ map (\x -> [LNeg x]) a
                           | otherwise = makeProb $ (impl a b) ++ (impl b a)
    where impl ant con = map (\lit -> (LNeg lit):(map LPos con)) ant
          ltrue = any isTrue a
          rtrue = any isTrue b
          lfalse = all isFalse a
          rfalse = all isFalse b
          vars = nub $ filter isVar (a ++ b)
          makeProb = makeProblemWith vars

--returns true if the left side is strictly greater than the right side
dominates :: Eq a => [Literal a] -> [Literal a] -> Bool
dominates l r = null $ (pos r) \\ (pos l)
    where pos = filter isPos



--finds all minimal non-trivial solutions being carful to never
--pattern match on a solution that we know is not minimal
--minimals' :: [[Literal a]] -> [Literal a] -> Solutions a -> [[Literal a]]
minimals' ss cur (Sat True) | all isNeg cur = ss
                            | otherwise     = cur:ss
minimals' ss cur (Sat False) = ss
minimals' ss cur (Sols i s1 s2) | any (((LPos i):cur) `dominates`) mins = mins
                                | otherwise = minimals' mins ((LPos i):cur) s2
    where mins = minimals' ss ((LNeg i):cur) s1


--finds the trivial solution
trivialSol (Sols i s _) = map ((LNeg i) :) (trivialSol s)
trivialSol (Sat True)   = [[]]
trivialSol (Sat False)  = []


--finds all minimal solutions or the trivial solution if no nontrivial ones
--exist
--minimals :: Eq a => Solutions a -> [[Literal a]]
minimals sols | null minsols = trivialSol sols
              | otherwise    = minsols
    where minsols = minimals' [] [] sols

--simplifies a term by removing all empties
simplify e = refoldTerms (unfoldTerm e)


--uses vget to get the term being solved for and converts a solution
--into a substitution
--conv :: State [b] (f a) -> [Literal (f a)] -> [SimpleEquation (f a)]
conv vget sol = vget >>= \var -> return $ map (convVar var) sol
    where convVar var term | isPos term = (getVar term) :==: var
                           | otherwise  = (getVar term) :==: mempty


--adds substitutions togethor (in the way that adding solutions togethor)
--maps to under the homomorphism that takes solutions into substitutions
subadd :: (Eq m, Monoid m) => [SimpleEquation m] -> [SimpleEquation m] -> [SimpleEquation m]
subadd a b = like ++ unlike
    where like = [x :==: ((a' `mappend` b'))| (x :==: a') <- a, (y :==: b') <- b, x == y]
          unlike = filter (not . (`elem` (map eqleft like)) . eqleft) (a ++ b)
          eqleft (l :==: _) = l


--converts our internal equation represnetation to our external
toSub :: (Typeable a, FirstOrder f) => [SimpleEquation (f a)] -> [Equation f]
toSub []              = []
toSub ((x :==: y):xs) = (x :=: y):(toSub xs)

popVar :: State [EveryPig f] (f a)
popVar = do
    v <- pop
    return $ unEveryPig v


--solves a homogenous equation
solveHomoEq :: ACUI f a => SimpleEquation [f a] -> State [EveryPig f] [SimpleEquation (f a)]
solveHomoEq eq = do
    let mins = minimals . search . toSatProblem $ eq
    minSols <- mapM (conv popVar) mins
    let homosol = foldl subadd [] minSols
    return homosol

--solves an inhomogenous equation for a specific constant
solveInHomoEq :: ACUI f a => f a -> SimpleEquation [f a] -> State [EveryPig f] [[SimpleEquation (f a)]]
solveInHomoEq c eq = do
  let mins = minimals . search . toSatProblem $ eq
  minSols <- mapM (conv (return c)) mins
  return minSols

--finds all solutions to a = b
acuiUnify :: ACUI f a => f a -> f a -> State [EveryPig f] [[Equation f]]
acuiUnify a b = do
    let l = unfoldTerm a
    let r = unfoldTerm b
    let homo = homogenous (l :==: r)
    homosol <- solveHomoEq homo --solve the homogenous equation
    let inhomos = inhomogenous (l :==: r) --find all inhomogenous equations
    inhomosolss <- mapM (uncurry solveInHomoEq) inhomos --solve each one
    let sols = bigCrossWith subadd [homosol] inhomosolss --combine inhomo sols
    return $ map (toSub . map (eqmap simplify)) sols --simplify the solutions
