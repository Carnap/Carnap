{-#LANGUAGE TypeOperators, ScopedTypeVariables, FunctionalDependencies, GADTs, ExplicitForAll, RankNTypes, MultiParamTypeClasses, FlexibleContexts, PatternSynonyms #-}

module Carnap.Core.Unification.Combination (
  LabelPair(LabelPair), Labeling, UniFunction, Combineable(..),
  labelings, getVars, purify, findAllAliens, pureAbstract, partitions,
  substitutions, getLabels, combine,  typeGroup, weave,
  hasBackEdge, findNodes, closure, buildGraph, validSub,
  getEqLabel, solveEqs, groupEqBy
  --testing 
  , doSubs
) where

import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification
import Carnap.Core.Util
import Control.Monad.State
import Data.Typeable
import Data.Type.Equality
import Data.List
import Data.Function
import Data.Proxy

--this is really hard to test with
data LabelPair f label where
    LabelPair :: f a -> label -> LabelPair f label

type Labeling f label = [LabelPair f label]

data ComboPig f where
    ComboPig :: (Typeable a) => f a -> ComboPig f

findVar :: Combineable f label => f a -> [LabelPair f label] -> label -> label
findVar v []                        def           = def
findVar v ((LabelPair v' lbl):lbls) def | v =* v'   = lbl
                                        | otherwise = findVar v lbls def

type UniFunction f m = (forall a. f a -> Bool) -> [Equation f] -> m [[Equation f]]

class (FirstOrder f, Ord label, Eq label) => Combineable f label | f -> label where
    getLabel :: f a -> label
    getAlgo :: MonadVar f m => label -> UniFunction f m
    replaceChild :: f a -> EveryPig f -> Int -> f a

--first we need to split apart the terms into multiple equations
-- abstract :: (MonadVar f m, Typeable a, Combineable f label) => f a -> m (f a, [Equation f])
-- abstract term
--     | isVar term = return $ (term, [])
--     | otherwise = do
--     pureTerm <- foldM replace term (zip [0..] (decompose term term))
--     return (pureTerm, makeEqs (pureTerm :=: term)) --finally we need the actual equations
--     where makeEqs (a :=: b) | sameHead a b = decompose a b >>= makeEqs
--                             | otherwise    = [a :=: b]
--           replace tm (n, (l :=: _))
--               | isVar l   = return tm
--               | otherwise = freshPig >>= \v -> return $ replaceChild tm v n

--this breaks down a set of equations into so called "pure" equations
--namely they only contain function symbols from a single equational theory
-- pureAbstract :: (MonadVar f m, Combineable f label) => [Equation f] -> m [Equation f]
-- pureAbstract []              = return []
-- pureAbstract ((a :=: b):eqs) = do
--     (pureA, newA) <- abstract a
--     (pureB, newB) <- abstract b
--     v <- freshPig
--     rest <- pureAbstract $ newA ++ newB ++ eqs
--     let top = if isVar pureA || isVar pureB
--               then [pureA :=: pureB]
--               else [unEveryPig v :=: pureA, unEveryPig v :=: pureB]
--     return (top ++ rest)

--this decomposes a term into a term, minus a subterm x, and an equation
castOut:: (MonadVar f m, Typeable a, Typeable b, Combineable f label) => f b -> f a -> m (f a, Equation f)
castOut x y = do v <- fresh
                 --replace x with v in y
                 let y' = subst x v y
                 return (y', v :=: x)

--given a system of equations, returns an equivalent system of
--pureEquations (in which every equation contains only terms from a single
--theory), with no redundant equations.
pureAbstract :: (MonadVar f m, Combineable f label) => [Equation f] -> m [Equation f]
pureAbstract [] = return []
pureAbstract ((a :=: b):eqs) = do
        (a',aeqs) <- purify a
        (b',beqs) <- purify b
        eqs' <- pureAbstract eqs
        -- trivial equations break things; we remove them here.
        let (_, final) = deTrivialize (aeqs ++ beqs ++ eqs')
        if getLabel a' == getLabel b' 
            then return $ (a' :=: b'):final
            else do split <- split a' b'
                    return $ split ++ final
    where split x y = do v <- fresh
                         return [v :=: x, v :=: y]

purify :: (MonadVar f m, Typeable a, Combineable f label) => f a -> m (f a, [Equation f])
purify x
    | isVar x = return (x,[])
    | otherwise = 
        do let xl = getLabel x
           let xchildren = nub $ disintegrate x
           --the code gets weirdly nationalistic at this point.
           let allaliens = findAllAliens xl xchildren 
           (pureTerm, impurities) <- deport allaliens x
           purity <- pureAbstract impurities
           return (pureTerm, purity)

    where 
          deport :: (MonadVar f m, Typeable a, Combineable f label) => 
                [Equation f] -> f a -> m (f a, [Equation f])
          deport [] x' = return (x',[])
          deport ((a:=:_):as) x' = do (out , eq) <- castOut a x'
                                      (out', eqs') <- deport as out
                                      return (out', eq:eqs')

findAllAliens :: (Combineable f label) => label -> [Equation f] -> [Equation f]
findAllAliens lbl [] = []
findAllAliens lbl x = 
  let (terrans,aliens) = partition (\(y:=:_) -> getLabel y == lbl) x in
      aliens ++ findAllAliens lbl 
        (concat $ map (\(y:=:_) -> disintegrate y) terrans) 

disintegrate x = decompose x x     

--compose the list functor with another functor
instance Schematizable f => Schematizable (ListComp f) where
    schematize (ListComp l) [] = "[" ++ intercalate ", " (map (\x -> schematize x []) l) ++ "]"

--take a list of AnyPigs and group them by their type
typeGroup :: [AnyPig f] -> [ComboPig (ListComp f)]
typeGroup l = foldr insert [] l
    where insert ax@(AnyPig (x :: f a)) (ay@(ComboPig (ListComp (y :: [f b]))):ys) = case eqT :: Maybe (a :~: b) of
              Just Refl                   -> (ComboPig (ListComp (x : y))):ys
              Nothing                     -> ay : (insert ax ys)
          insert (AnyPig (x :: f a))    [] = [ComboPig $ ListComp [x]]

--finds all partitions of a list
partitions [] = [[]]
partitions (x:xs) = [[x]:p | p <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

--finds all substitutions of AnyPig varibles
substitutions :: HigherOrder f => [AnyPig f] -> [[Equation f]]
substitutions [] = [[]]
substitutions vars = bigCrossWithH (++) (map parts (typeGroup vars))
    where parts (ComboPig (ListComp l)) = map part2Sub (partitions l)
          --conerts a partition to a substitution
          part2Sub ((x:xs):xss) = (map (x :=:) xs) ++ part2Sub xss
          part2Sub []           = []

--finds all lebeling functions
labelings :: Combineable f label => [AnyPig f] -> [label] -> [Labeling f label]
labelings ((AnyPig x):domain) range = [(LabelPair x l):f | f <- labelings domain range, l <- range]
labelings []                  range = [[]]

--trys to find a back edge by checking if a node is it's own closure
hasBackEdge :: (FirstOrder f) => [AnyPig f] -> [(AnyPig f, [AnyPig f])] -> Bool
hasBackEdge nodes gph = any (\n -> any (== n) (closure [] gph n)) nodes

--finds all adjacent nodes
findNodes n ((n1, n2):gph) | n == n1   = n2 ++ findNodes n gph
                           | otherwise = findNodes n gph
findNodes n []                         = []

--finds all nodes reachable from a start node
--closure :: (FirstOrder f) => [AnyPig f] -> [(AnyPig f, [AnyPig f])] -> AnyPig f -> [AnyPig f]
closure visit gph node
    | any (== node) visit = findNodes node gph
    | otherwise           = case findNodes node gph of
        []     -> []
        childs -> nub $ childs ++ concatMap (\c -> closure (node:visit) gph c) childs

--builds a graph out of a set of equations in the correct manner
buildGraph ((v :=: e):eqs) = (AnyPig v, freeVars e) : buildGraph eqs
buildGraph []              = []

--checks if a subsitution is valid by converting it to a graph and checking
--for back edges
validSub :: Combineable f label => [Equation f] -> Bool
validSub eqs = not (hasBackEdge (getVars eqs) (buildGraph eqs))

--gets all the varibles from a set of equations
getVars :: Combineable f label => [Equation f] -> [AnyPig f]
getVars eqs = nubBy (==) (go eqs)
    where go ((a :=: b):eqs) = freeVars a ++ freeVars b ++ go eqs
          go []              = []

--get's all the labels of every equation
getLabels :: Combineable f label => [Equation f] -> [label]
getLabels =  map labelsOfGroups . groupByLabel 
    where labelsOfGroups (x:xs) = getEqLabel x

--XXX:Weirdly, this version seems faster on big negative cases
--getLabels = nub . map getEqLabel

--get's a associated theory label of an equation
getEqLabel :: Combineable f label => Equation f -> label
getEqLabel (a :=: b) | isVar a   = getLabel b
                     | otherwise = getLabel a

--solves a system of equations for a fixed theory if given a labeling
solveEqs :: forall f m label. (MonadVar f m, Combineable f label) => Labeling f label -> [Equation f] -> m [[Equation f]]
solveEqs _        []       = return [[]]
solveEqs labeling (eq:eqs) = getAlgo lbl varConst (eq:eqs)
    where varConst :: forall a. f a -> Bool
          varConst v = lbl /= findVar v labeling lbl
          lbl = getEqLabel eq

--weaves a though a 2D list making a 1D path simalar to how you map
--pairs of natural numbers to natural numbers
--this *should* be able to weave any length lists even infinite lists
weave xss = go xss 1
    where step xss          0 = (xss, [])
          step []           _ = ([],  [])
          step ((x:xs):xss) n = let (rest, l) = step xss (n - 1) in (xs : rest, x : l)
          step ([]:xss)     n = step xss n
          go []  _ = []
          go xss n = let (rest, l) = step xss n in l ++ go rest (n + 1)

deTrivialize :: (Combineable f label) => [Equation f] -> ([Equation f],[Equation f])
deTrivialize eqs = let (trivial, nontrivial) = partition isTrivial eqs 
                       final = mapAll (applySub trivial) nontrivial 
                       in (trivial, final)
            where isTrivial (a :=: b) = isVar a && isVar b

groupByLabel :: (Combineable f label) => [Equation f] -> [[Equation f]]
groupByLabel eqs = groupBy ((==) `on` getEqLabel) (sortOn getEqLabel eqs)

groupEqBy :: (Equation f -> Equation f -> Bool) -> [Equation f] -> [[Equation f]]
groupEqBy r [] = []
groupEqBy r (x:xs) = sameAsHead:(groupEqBy r rest)
    where (sameAsHead, rest) = partition (r x) (x:xs)


doSubs :: (MonadVar f m, Combineable f label) => [Equation f] -> [Equation f] -> m [[[Equation f]]]
doSubs sub pureeqs = do let pureSubbedEqs = mapAll (applySub sub) pureeqs
                        let vars = getVars pureSubbedEqs
                        let labels = getLabels pureSubbedEqs
                        let labelingsList = labelings vars labels
                        let eqGroups = groupByLabel pureSubbedEqs
                        let doLabelings lbling = do
                               solsByGroup <- mapM (solveEqs lbling) eqGroups
                               return $ map (sub ++) (bigCrossWithH (++) solsByGroup)
                        mapM doLabelings labelingsList

--this is some dense code, I'm displeased with dense it is in fact
--it would be less dense if I could handle this case by case in a loop
--yielding ansers as I went such that the results were woven togethor for me
--I might refactor all of this to do that
combine :: (MonadVar f m, HigherOrder f, Combineable f label) => [Equation f] -> m [[Equation f]]
combine eqs = do
    let (trivs,eqs') = deTrivialize eqs
    pureEqs <- pureAbstract eqs
    let eqsByType = groupEqBy sameTypeEq pureEqs
    let varsByType = map getVars eqsByType
    --XXX: the following hack, focusing on only substitutional variables, seems
    --to help with the sequent case a lot. Need to check if it is correct.
    --No counterexamples yet.
    --let vars' = filter (\x -> head (show x) == 'α') vars 
    let subsByType = map substitutions varsByType
    let subs = bigCrossWithH (++) subsByType
    sols2d <- mapM (\x -> doSubs x pureEqs) subs
    return $ map (++ trivs) $ weave . weave $ sols2d 
