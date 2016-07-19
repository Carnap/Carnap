{-#LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Carnap.Core.ModelChecking.SAT (
  SatProblem, unitProp, units, unassigned, valuation, evaluate,
  ListSat, neg, getVar, Literal(LPos, LNeg), search, enumerate,
  makeProblem, makeProblemWith, isPos, isNeg, Solutions(Sat, Sols)
) where

import Data.List
import Control.Monad
import Control.Monad.State

data Literal a = LPos a
               | LNeg a
    deriving(Eq, Ord, Show)

neg (LPos x) = LNeg x
neg (LNeg x) = LPos x

getVar (LPos x) = x
getVar (LNeg x) = x

isPos (LPos _) = True
isPos _        = False

isNeg = not . isPos

class SatProblem t a | t -> a where
    unitProp :: Literal a -> t -> t
    units :: t -> [Literal a]
    unassigned :: t -> [a]
    valuation :: t -> [Literal a]
    evaluate :: t -> Bool

data ListSat a = ListSat [Literal a] [a] [[Literal a]]
               | ListSatFalse
    deriving(Show)

makeProblem prob = ListSat [] (nub $ prob >>= map getVar) prob
makeProblemWith with prob = ListSat [] (nub $ with ++ (prob >>= map getVar)) prob

instance Eq a => SatProblem (ListSat a) a where
    evaluate ListSatFalse = False
    evaluate (ListSat vs [] cs) = all (any (`elem` vs)) cs
    evaluate _                  = error "You cannot evaluatae a term with unassigned literals"

    valuation ListSatFalse     = []
    valuation (ListSat vs _ _) = vs

    unassigned ListSatFalse     = []
    unassigned (ListSat _ us _) = us

    units ListSatFalse     = []
    units (ListSat _ _ cs) = map head . filter single $ cs
        where single [_] = True
              single _   = False

    unitProp _ ListSatFalse = ListSatFalse
    unitProp u (ListSat vs us cs) = case csM of
        Just cs' -> ListSat (u : vs) (delete (getVar u) us) cs'
        Nothing -> ListSatFalse
        where csM = filterM pass . map (delete (neg u)) $ cs
              pass clause = case clause of
                  [] -> Nothing
                  _ -> Just . not $ u `elem` clause

cascadeUnits :: SatProblem t a => t -> (t, [Literal a])
cascadeUnits s | null us   = (s, [])
               | otherwise = let (s', us') = cascadeUnits $ foldr unitProp s us
                             in (s', us ++ us')
               where us = units s

--this is nice feature/optimization. by representing our solutions as a tree
--we can prune whole search paths simply by not pattern matching on certian
--branches. this allows us to decouple finding minimal solutions from searching
--for solutions. so this is both a good design choice *and* an optimization
data Solutions a = Sat Bool
                 | Sols a (Solutions a) (Solutions a)
    deriving(Show)

valuation2sol []     v        = v
valuation2sol ((LNeg x):xs) v = Sols x (valuation2sol xs v) (Sat False)
valuation2sol ((LPos x):xs) v = Sols x (Sat False) (valuation2sol xs v)


search :: SatProblem t a => t -> Solutions a
search s = let (s', us) = cascadeUnits s in case unassigned s' of
    (l:_) -> valuation2sol us $ Sols l (search $ unitProp (LNeg l) s') (search $ unitProp (LPos l) s')
    []    -> if evaluate s' then valuation2sol us (Sat True) else Sat False


enumerate ls (Sols l s1 s2) = enumerate (LNeg l : ls) s1 ++ enumerate (LPos l : ls) s2
enumerate ls (Sat True)     = [ls]
enumerate _  _              = []

{-
--optimizations to consider
--2. find units when unit propigating and store them at the top so that
--   finding the head of the units list happens more quickly
--3. use a different SAT problem representation
--4. use conflict driven clause learning (this is a big step forward)
--5. select which of the unassigneds to first propogate
--6. it might be possible to propogate all units more efficently than to cascade
--   a single
-}
