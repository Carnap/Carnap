{-#LANGUAGE TypeOperators, ScopedTypeVariables, FunctionalDependencies, GADTs, ExplicitForAll, RankNTypes, MultiParamTypeClasses, FlexibleContexts, PatternSynonyms #-}

module Carnap.Core.Unification.Combination (
  LabelPair(LabelPair), Labeling, UniFunction, Combineable,
  labelings, getVars,
) where


import Carnap.Core.Unification.Unification
import Carnap.Core.Util
import Control.Monad.State
import Data.Typeable
import Data.Type.Equality
import Data.List
import Data.Function
import Data.Proxy

data LabelPair f where
    LabelPair :: Combineable f label => f a -> label -> LabelPair f

type Labeling f = [LabelPair f]

type UniFunction f = Labeling f -> [Equation f] -> State [EveryPig f] [[Equation f]]

class (FirstOrder f, Eq label) => Combineable f label | f -> label where
    getLabel :: f a -> label
    getAlgo :: label -> UniFunction f
    replaceChild :: f a -> EveryPig f -> Int -> f a

--first we need to split apart the terms into multiple equations
abstract :: (Typeable a, Combineable f label) => f a -> State [EveryPig f] (f a, [Equation f])
abstract term = do
    pureTerm <- foldM replace term (zip [0..] (decompose term term))
    return (pureTerm, makeEqs (pureTerm :=: term)) --finally we need the actual equations
    where makeEqs (a :=: b) | sameHead a b = decompose a b >>= makeEqs
                            | otherwise    = [a :=: b]
          replace tm (n, (l :=: _))
              | getLabel l /= getLabel tm = pop >>= \v -> return $ replaceChild tm v n
              | otherwise                 = return tm

--this breaks down a set of equations into so called "pure" equations
--namely they only contain function symbols from a single equational theory
pureAbstract :: Combineable f label => [Equation f] -> State [EveryPig f] [Equation f]
pureAbstract ((a :=: b):eqs) = do
    (pureA, newA) <- abstract a
    (pureB, newB) <- abstract b
    v <- pop
    rest <- pureAbstract $ newA ++ newB ++ eqs
    let top = [unEveryPig v :=: pureA, unEveryPig v :=: pureB]
    return (top ++ rest)

--this gives bell's number answers

--compose the list functor with another functor
data ListComp f a where
    ListComp :: [f a] -> ListComp f a

--take a list of AnyPigs and group them by their type
typeGroup :: [AnyPig f] -> [AnyPig (ListComp f)]
typeGroup l = foldr insert [] l
    where insert ax@(AnyPig (x :: f a)) (ay@(AnyPig (ListComp (y :: [f b]))):ys) = case eqT :: Maybe (a :~: b) of
              Just Refl                   -> (AnyPig (ListComp (x : y))):ys
              Nothing                     -> ay : (insert ax ys)
          insert (AnyPig (x :: f a))    [] = [AnyPig $ ListComp [x]]

--finds all partitions of a list
partitions :: [f a] -> [[[f a]]]
partitions [] = [[]]
partitions (x:xs) = [[x]:p | p <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

--conerts a partitution to a substitution
part2Sub ((x:xs):xss) = (map (x :=:) xs) ++ part2Sub xss
part2Sub []           = []

--finds all substitutions of AnyPig varibles
substitutions :: FirstOrder f => [AnyPig f] -> [[Equation f]]
substitutions vars = bigCrossWithH (++) (map parts (typeGroup vars))
    where parts (AnyPig (ListComp l)) = map part2Sub (partitions l)

--finds all lebeling functions
labelings :: Combineable f label => [AnyPig f] -> [label] -> [Labeling f]
labelings ((AnyPig x):domain) range = [(LabelPair x l):f | f <- labelings domain range, l <- range]

equiv :: (FirstOrder f) => AnyPig f -> AnyPig f -> Bool
equiv (AnyPig (x :: f a)) (AnyPig (y :: f b)) = case eqT :: Maybe (a :~: b) of
    Just Refl -> sameHead x y && all (\(a :=: b) -> equiv (AnyPig a) (AnyPig b)) (decompose x y)
    Nothing   -> False

--depth first search to detect cycle
hasBackEdge :: (FirstOrder f) => [AnyPig f] -> [(AnyPig f, [AnyPig f])] -> Bool
hasBackEdge nodes gph = any (\n -> any (equiv n) (closure [] gph n)) nodes

findNodes n ((n1, n2):gph) | equiv n n1 = n2 ++ findNodes n gph
                           | otherwise  = findNodes n gph
findNodes n []                          = []

closure :: (FirstOrder f) => [AnyPig f] -> [(AnyPig f, [AnyPig f])] -> AnyPig f -> [AnyPig f]
closure visit gph node
    | any (equiv node) visit = visit
    | otherwise              = case findNodes node gph of
        []     -> visit
        childs -> concatMap (\c -> closure (c:visit) gph c) childs

buildGraph ((v :=: e):eqs) = (AnyPig v, freeVars e) : buildGraph eqs

validSub :: Combineable f label => [Equation f] -> Bool
validSub eqs = not (hasBackEdge (getVars eqs) (buildGraph eqs))

getVars :: Combineable f label => [Equation f] -> [AnyPig f]
getVars = undefined

getLabels :: Combineable f label => [Equation f] -> [label]
getLabels = nub . map getEqLabel
-- pureAbstract -> getVars -> partitions -> functions
-- -> unification on each equation -> cycle checking

getEqLabel :: Combineable f label => Equation f -> label
getEqLabel (a :=: b) | isVar a   = getLabel b
                     | otherwise = getLabel a

solveEqs :: Combineable f label => Labeling f -> [Equation f] -> State [EveryPig f] [[Equation f]]
solveEqs labeling (eq:eqs) = getAlgo (getEqLabel eq) labeling (eq:eqs)

--weaves a though a 2D list making a 1D path simalar to how you map
--pairs of natural numbers to natural numbers
weave xss = go xss 1
    where step xss          0 = (xss, [])
          step []           _ = ([],  [])
          step ((x:xs):xss) n = let (rest, l) = step xss (n - 1) in (xs : rest, x : l)
          step ([]:xss)     n = step xss n
          go []  _ = []
          go xss n = let (rest, l) = step xss n in l ++ go rest (n + 1)

--this is some dense code
combine :: Combineable f label => [Equation f] -> State [EveryPig f] [[Equation f]]
combine eqs = do
    pureEqs <- pureAbstract eqs
    let vars = getVars pureEqs
    let subs = substitutions vars
    let pureSubbedEqs = map (\sub -> mapAll (applySub sub) pureEqs) subs
    let labelFuncs = map (\eq -> labelings (getVars eq) (getLabels pureEqs)) pureSubbedEqs
    let eqGroups = map (groupBy ((==) `on` getEqLabel)) pureSubbedEqs
    let combineTheory eqg l = mapM (solveEqs l) eqg >>= (return . concat)
    sols2d <- mapM (\(l, eqg) -> mapM (combineTheory eqg) l) (zip labelFuncs eqGroups)
    --sols2d is indexed by labelings on the outside and subsitutions on the inside
    --sols2d is isomorphim to (subs, labelFuncs) -> solutions
    let sols = weave (weave sols2d) --weave the set of solutions missing no solution even if solutions are infinite
    return $ filter validSub sols --filter out ones that have cycles
