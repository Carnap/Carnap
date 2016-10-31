{-#LANGUAGE ImpredicativeTypes, ScopedTypeVariables, FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Huet
        ( 
        )
    where

import Carnap.Core.Util
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification 
import Data.Typeable
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Logic
import Control.Monad.Trans.Class as M

-- | simplfies a set of equations, returning a set of equations with the same
--set of solutions, but no rigid-rigid equations---or Nothing, in the case
--where the set of equations has no solutions.
simplify eqs = 
        do filtered <- filterM rigidRigid eqs
           case filtered of
               [] -> Just eqs
               rr -> do failCheck rr 
                        >>= massDecompose 
                        >>= simplify
                        >>= (\x -> return $ (filter (not . \x -> elem x rr) eqs) ++ x)
    where failCheck l = if and (map (\(x:=:y) -> sameHead x y) l) 
                           then Just l
                           else Nothing
          massDecompose l = Just $ concat $ map (\(x:=:y) -> decompose x y) l

-- | returns true on rigid-rigid equations between terms in βη long normal form
--(since these are guaranteed to have heads that are either constants or
--variables).

rigidRigid :: (HigherOrder f, MonadVar f m)  => Equation f -> m Bool
rigidRigid (x:=:y) = (&&) <$> constHead x [] <*> constHead y []
    where constHead ::  (HigherOrder f, MonadVar f m, Typeable a) => f a -> [AnyPig f] -> m Bool
          constHead x bv = case castLam x of
           (Just (ExtLam l Refl)) -> do lv <- fresh
                                        constHead (l .$. lv) ((AnyPig l):bv)
           _ ->  do (h, _) <- guillotine x
                    return $ not (freeVar h)
           where freeVar p@(AnyPig x) = isVar x && not (p `elem` bv)
       
abstractEq :: HigherOrder f => AnyPig f -> AnyPig f -> Equation f -> Maybe (Equation f)
abstractEq (AnyPig (v :: f a)) (AnyPig (v' :: f b)) (t :=:t') = 
        case eqT :: Maybe (a :~: b) of
            Just Refl -> Just $ (lam $ \x -> subst v x t) :=: (lam $ \x -> subst v' x t')
            Nothing -> Nothing

-- XXX : This needs to take place in a fresh variable monad. Should use
--a new type of fresh variable for fresh unification variables, in order to
--avoid issues with substitution.
--
-- XXX : the case-statement mess here could probably be improved by using
-- view-patterns.
--
-- XXX : excessive eqT use could probably be cleand up.
--
-- | given a an oriented flexible/rigid equation (with the flexible side on
-- the left), this indeterministically returns a simplified equation
-- resulting from the generate rule (not doing the βη-reduction), and the
-- associated substituitional equation. 
--
--bad behavior can be expected when given a rigid/rigid, flexible/flexible,
--or rigid/flexible equation.
generate :: (MonadVar f m, HigherOrder f) => Equation f -> LogicT m (Equation f,Equation f)
generate ((x :: f a) :=: y) = --accumulator for projection terms
         do case (castLam x, castLam y) of
                (Just (ExtLam l Refl),Just (ExtLam l' Refl)) -> 
                    do fv <- M.lift fresh
                       fv' <- M.lift fresh
                       (eq, sub) <- generate ((l .$. fv) :=:  (l' .$. fv'))
                       let (Just eq') = abstractEq (AnyPig fv) (AnyPig fv') eq
                       return (eq', sub)
                (Nothing, Nothing) -> 
                    do (AnyPig (headX :: f t1), projterms) <- guillotine x
                       let vbranches = map (M.lift . project projterms) projterms
                       let hbranch = M.lift $ imitate projterms (AnyPig y)
                       vpig <- foldr mplus mzero vbranches 
                       (AnyPig (newTerm :: f t5)) <- hbranch `mplus` (return vpig)
                       gappyX <- M.lift $ safesubst headX x
                       case eqT :: Maybe (t5 :~: t1) of
                           Just Refl -> return (gappyX newTerm :=:y,headX:=:newTerm)
                           Nothing -> mzero
          where project = projectOrImitate
                imitate = projectOrImitate

guillotine :: (HigherOrder f, Monad m,Typeable a) => f a -> m (AnyPig f, [AnyPig f])
guillotine x = basket (AnyPig x) []
            where basket (AnyPig x) pigs = case matchApp x of
                      Just (ExtApp h t) -> basket (AnyPig h) ((AnyPig t):pigs)
                      Nothing -> return (AnyPig x,pigs)

--recursively performs a surgery on a term (either a projection term or the
--body of the rhs), eventually replacing every part of the term with an
--appropriate chunk of variables.
--
--Note that the projection term will not be of the same type as the return
--value. Hence, we need an AnyPig here.
projectOrImitate :: (MonadVar f m, HigherOrder f) => [AnyPig f] -> AnyPig f ->  m (AnyPig f)
projectOrImitate projterms (AnyPig term) = 
        do pvs <- toVars projterms
           body <- handleBody pvs term
           projection <- bindAll pvs (AnyPig body)
           return projection
    where handleBody :: (MonadVar f m, HigherOrder f, Typeable a) => [AnyPig f] -> f a ->  m (f a)
          handleBody projvars term = case matchApp term of
               Nothing -> return term
               (Just (ExtApp h t)) -> do newInit <- handleBody projvars h
                                         freshArg <- genFreshArg projvars newInit
                                         return $ newInit .$. freshArg

toVars :: (MonadVar f m) => [AnyPig f] -> m [AnyPig f]
toVars (AnyPig (x :: f t):xs) = do y :: f t <- fresh 
                                   tail <- toVars xs
                                   return (AnyPig y:tail)

bindAll :: (HigherOrder f, MonadVar f m) => [AnyPig f] -> AnyPig f -> m (AnyPig f)
bindAll (AnyPig v :vs) (AnyPig body ) = 
            do f <- safesubst v body
               bindAll vs (AnyPig (lam f))
bindAll [] body = return body

--substitute f a in f b while avoiding collision of variables
safesubst :: (MonadVar f m) => f a -> f b -> m (f a -> f b)
safesubst x y = undefined

genFreshArg :: (MonadVar f m, HigherOrder f, Typeable a) => [AnyPig f] -> f (a -> b) -> m (f a)
genFreshArg projvars term =
        do (EveryPig head) <- freshPig 
           return $ attach head projvars
    where attach ::  (HigherOrder f, Typeable d) => (forall c .Typeable c => f c) -> [AnyPig f] -> f d
          attach h  ((AnyPig v):vs) = attach (h .$. v) vs
          attach h [] = h

--- | given x, y with no leading variables, this applies the generate rule
--to replace the old head of x with the new head

huetunify :: HigherOrder f
        => (forall a. f a -> Bool) --treat certain variables as constants
        -> [Equation f] --equations to be solved
        -> [Equation f] --accumulator for the substitution
        -> [[Equation f]]
huetunify varConst [] ss = Right ss
huetunify varConst es ss = 
        do let esFlex = simplify es
           return undefined

huetUnifySys :: (MonadVar f m, HigherOrder f) => (forall a. f a -> Bool) -> [Equation f] -> m [[Equation f]]
huetUnifySys = undefined

