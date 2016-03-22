module Carnap.Core.Unification.ACUI () where

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
        where csM = filterM pass . map (delete u) $ cs
              pass clause = case clause of
                  [] -> Nothing
                  _ -> Just . not $ u `elem` clause

--the basic algorithm I came up with is based on DPLL

--1. cascade all units until there are no more units
--2. select a literal and call l. the order in which literals is selected is
--   important to performance. choose varibles to go early that have a higher
--   chance of causing unit cascades when assigned false
--3. assign that literal false and find all solutions
--4. given the current assignment and solutons determine weather it is worth it
--   to search for this 1. if adding this to valuation dominates all solutions
--   then there is no point in searching because all further solutions will be
--   bigger than one of the current solutions


compSols :: [Int] -> [Int] -> Bool
compSols x y = not . null $ (filter (> 0) y) \\ (filter (> 0) x)

worthIt :: [Int] -> [[Int]] -> Bool
worthIt proposal sols = all (compSols proposal) sols

cascadeUnits :: SatProblem t => t -> t
cascadeUnits s | null us   = s
               | otherwise = cascadeUnits $ foldr unitProp s us
               where us = units s

--search :: SatProblem t => t -> State [[Int]] ()
--search s = do
    --let s' = cascadeUnits s --first flush out all of the units
    --case unassigned s' of
      --  (l:_) -> do search (unitProp (negate l) s')
        --            vals <- get
          --          search (unitProp l s') vals
            --        return ()
        --[]    -> return ()
    --case unassigned s' where
      --  (l:_) -> runIdentity $ do
        --    let sols' = search (unitProp (negate l) s') sols
          --  let vals = map valuation sols'
            --let sols'' = search (unitProp l s') vals in
            --if worthIt (l : valutation s') vals
              --then sols'
              --else sols' ++ sols''
        --[]    -> if evaluate s' then [s'] else []
