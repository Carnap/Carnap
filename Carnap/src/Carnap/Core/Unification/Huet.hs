{-#LANGUAGE ImpredicativeTypes, ScopedTypeVariables, FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Huet
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
simplify ::(HigherOrder f, MonadVar f m) => [Equation f] -> LogicT m [Equation f]
simplify eqs = 
        do filtered <- M.lift $ filterM rigidRigid eqs
           case filtered of
               [] -> return eqs
               rr -> do failCheck rr 
                        >>= massDecompose 
                        >>= simplify
                        >>= (\x -> return $ (filter (not . \x -> elem x rr) eqs) ++ x)
    where failCheck l = if and (map (\(x:=:y) -> sameHead x y) l) 
                           then return l
                           else mzero
          massDecompose l = return $ concat $ map (\(x:=:y) -> decompose x y) l

-- | returns true on rigid-rigid equations between terms in βη long normal form
--(since these are guaranteed to have heads that are either constants or
--variables).

rigidRigid :: (HigherOrder f, MonadVar f m)  => Equation f -> m Bool
rigidRigid (x:=:y) = (&&) <$> constHead x [] <*> constHead y []
    where constHead ::  (HigherOrder f, MonadVar f m, Typeable a) => f a -> [AnyPig f] -> m Bool
          constHead x bv = case castLam x of
           (Just (ExtLam l _)) -> do lv <- fresh
                                     constHead (l lv) ((AnyPig lv):bv)
           _ ->  do (h, _) <- guillotine x
                    return $ not (freeVar h)
           where freeVar p@(AnyPig x) = isVar x && not (p `elem` bv)
       
abstractEq :: (MonadPlus m, HigherOrder f) => AnyPig f -> AnyPig f -> Equation f -> m (Equation f)
abstractEq (AnyPig (v :: f a)) (AnyPig (v' :: f b)) (t :=:t') = 
        case eqT :: Maybe (a :~: b) of
            Just Refl -> return $ (lam $ \x -> subst v x t) :=: (lam $ \x -> subst v' x t')
            Nothing -> mzero

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
                       (eq, sub) <- generate $ (l fv) :=:  (l' fv')
                       eq' <-  abstractEq (AnyPig fv) (AnyPig fv') eq
                       return (eq', sub)
                (Nothing, Nothing) -> 
                    do (AnyPig (headX :: f t1), projterms) <- guillotine x
                       projvars <- M.lift $ toVars projterms
                       let vbranches = map (M.lift . project projvars) projvars
                       let hbranch = M.lift $ imitate projvars (AnyPig y)
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

--return "Nothing" in the do nothing case
betaReduce :: (HigherOrder f) => f a -> Maybe (f a)
betaReduce x = do (ExtApp h t) <- (matchApp x)
                  (ExtLam l Refl) <- (castLam h)
                  return (l t)

--return "Nothing" in the do nothing case
betaNormalize :: (HigherOrder f, MonadVar f m, Typeable a) => f a -> m (Maybe (f a))
betaNormalize x = case (castLam x) of
                     Just (ExtLam f Refl) -> 
                        do v <- fresh
                           inf <- betaNF (f v)
                           return $ Just (lam $ \x -> subst v x inf)
                     Nothing -> case (matchApp x) of
                        Just (ExtApp h t) -> do
                            mh <- betaNormalize h
                            mt <- betaNormalize t
                            case (mh,mt) of
                                (Just h', Just t') -> mbetaNF (h' .$. t') 
                                (Nothing, Just t') -> mbetaNF (h .$. t') 
                                (Just h', Nothing) -> mbetaNF (h' .$. t)
                                (Nothing, Nothing) -> 
                                    case betaReduce x of
                                        Nothing -> return Nothing
                                        Just x' -> mbetaNF x' 
                        Nothing -> return Nothing
        where mbetaNF x = do y <- betaNF x
                             return (Just y)

betaNF :: (HigherOrder f, MonadVar f m, Typeable a) => f a -> m (f a)
betaNF x = do nf <- betaNormalize x
              case nf of
                   Nothing -> return x
                   (Just y) -> return y


toLNF :: (HigherOrder f, MonadVar f m, Typeable a, EtaExpand m f a) => f a -> m (f a)
toLNF x = do bnf <- betaNF x
             case matchApp bnf of 
                Just (ExtApp h t) -> do t' <- toLNF t
                                        etaMaximize  (h .$. t')
                Nothing -> case (castLam bnf) of
                         Just (ExtLam f Refl) -> 
                            do v <- fresh
                               inf <- toLNF (f v)
                               return $ (lam $ \y -> subst v y inf)
                         Nothing -> etaMaximize bnf

etaMaximize :: (HigherOrder f, MonadVar f m, Typeable a, EtaExpand m f a) => f a -> m (f a)
etaMaximize x = do y <- etaExpand x
                   case y of 
                    Nothing -> return x
                    Just y' -> etaMaximize y'




--recursively performs a surgery on a term (either a projection term or the
--body of the rhs), eventually replacing every part of the term with an
--appropriate chunk of variables.
--
--Note that the projection term will not be of the same type as the return
--value. Hence, we need an AnyPig here.
projectOrImitate :: (MonadVar f m, HigherOrder f) => [AnyPig f] -> AnyPig f ->  m (AnyPig f)
projectOrImitate pvs (AnyPig term) = 
        do body <- handleBody pvs term
           projection <- bindAll pvs (AnyPig body)
           return projection

handleBody :: (MonadVar f m, HigherOrder f, Typeable a) => [AnyPig f] -> f a ->  m (f a)
handleBody projvars term = case matchApp term of
   Nothing -> return term
   (Just (ExtApp h t)) -> do newInit <- handleBody projvars h
                             freshArg <- genFreshArg projvars newInit
                             return $ newInit .$. freshArg

toVars :: (MonadVar f m) => [AnyPig f] -> m [AnyPig f]
toVars (AnyPig (x :: f t):xs) = do y :: f t <- fresh 
                                   tail <- toVars xs
                                   return (AnyPig y:tail)
toVars [] = return []

bindAll :: (HigherOrder f, MonadVar f m) => [AnyPig f] -> AnyPig f -> m (AnyPig f)
bindAll (AnyPig v :vs) (AnyPig body ) = 
            do f <- safesubst v body
               bindAll vs (AnyPig (lam f))
bindAll [] body = return body

--substitute f a in f b while avoiding collision of variables
safesubst :: (HigherOrder f, MonadVar f m, Typeable a, Typeable b) => f a -> f b -> m (f a -> f b)
safesubst (x :: f a) (y :: f b) = return $ \z -> subst x z y

genFreshArg :: (MonadVar f m, HigherOrder f, Typeable a) => [AnyPig f] -> f (a -> b) -> m (f a)
genFreshArg projvars term =
        do (EveryPig head) <- freshPig 
           return $ attach head projvars
    where attach ::  (HigherOrder f, Typeable d) => (forall c .Typeable c => f c) -> [AnyPig f] -> f d
          attach h  ((AnyPig v):vs) = attach (h .$. v) vs
          attach h [] = h

--- | given x, y with no leading variables, this applies the generate rule
--to replace the old head of x with the new head

-- huetunify :: HigherOrder f
--         => (forall a. f a -> Bool) --treat certain variables as constants
--         -> [Equation f] --equations to be solved
--         -> [Equation f] --accumulator for the substitution
--         -> [[Equation f]]
-- huetunify varConst [] ss = Right ss
-- huetunify varConst es ss = 
--         do let esFlex = simplify es
--            return undefined

huetUnifySys :: (MonadVar f m, HigherOrder f) => (forall a. f a -> Bool) -> [Equation f] -> m [[Equation f]]
huetUnifySys = undefined

