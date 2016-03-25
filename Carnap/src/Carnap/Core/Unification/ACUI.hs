module Carnap.Core.Unification.ACUI (
  SatProblem, unitProp, units, unassigned,valuation,evaluate,
  ListSat(ListSat), cascadeUnits, search
) where

import Data.List
import Control.Monad
import Control.Monad.State

--to solve ACUI unification with constants we need to be able to find
--all minimal solutions to a SAT problem

--there are different representations of a SatProblem that be more efficent
--because I don't know which will be most efficent and efficency might be a
--concern at some point I created a type class to represent what a SAT problem
--should be able to do so that the DPLL algorithm is independent of the SAT
--representation
class SatProblem t where
    unitProp :: Int -> t -> t
    units :: t -> [Int]
    unassigned :: t -> [Int]
    valuation :: t -> [Int]
    evaluate :: t -> Bool

data ListSat = ListSat [Int] [Int] [[Int]]
             | ListSatFalse
    deriving(Show)

instance SatProblem ListSat where
    evaluate ListSatFalse       = False
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
        Just cs' -> ListSat (u : vs) (delete (abs u) us) cs'
        Nothing -> ListSatFalse
        where csM = filterM pass . map (delete (negate u)) $ cs
              pass clause = case clause of
                  [] -> Nothing
                  _ -> Just . not $ u `elem` clause

cascadeUnits :: SatProblem t => t -> (t, [Int])
cascadeUnits s | null us   = (s, [])
               | otherwise = let (s', us') = cascadeUnits $ foldr unitProp s us
                             in (s', us ++ us')
               where us = units s

--this is nice feature/optimization. by representing our solutions as a tree
--we can prune whole search paths simply by not pattern matching on certian
--branches. this allows us to decouple finding minimal solutions from searching
--for solutions. so this is both a good design choice *and* an optimization
data Solutions = Sat Bool
               | Sols Int Solutions Solutions
    deriving(Show)

valuation2sol []     v             = v
valuation2sol (x:xs) v | x < 0     = Sols (abs x) (valuation2sol xs v) (Sat False)
                       | otherwise = Sols x (Sat False) (valuation2sol xs v)

search :: SatProblem t => t -> Solutions
search s = let (s', us) = cascadeUnits s in case unassigned s' of
    (l:_) -> valuation2sol us $ Sols l (search $ unitProp (negate l) s') (search $ unitProp l s')
    []    -> if evaluate s' then valuation2sol us (Sat True) else Sat False

enumerate (Sols l s1 s2) ls = enumerate s1 ((0-l) : ls) ++ enumerate s2 (l : ls)
enumerate (Sat True)     ls = [ls]
enumerate _              _  = []

--optimizations to consider
--1. have evaluate return true in the non-false case
--2. find units when unit propigating and store them at the top so that
--   finding the head of the units list happens more quickly
--3. use a different SAT problem representation
--4. use conflict driven clause learning (this is a big step forward)
--5. select which of the unassigneds to first propogate
--6. it might be possible to propogate all units more efficently than to cascade
--   a single
