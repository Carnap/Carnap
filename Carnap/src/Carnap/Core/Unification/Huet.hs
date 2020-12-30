{-#LANGUAGE ImpredicativeTypes, ScopedTypeVariables, FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Huet (huetMatchSys) where

import Carnap.Core.Util
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification 
import Data.Typeable
import Data.List (nub)
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Trans.Class as M

-- | simplifies a set of equations, returning a set of equations with the same
--set of solutions, but no rigid-rigid equations---or Nothing, in the case
--where the set of equations has no solutions.
simplify ::(HigherOrder f, MonadVar f m) => [Equation f] -> LogicT m [Equation f]
simplify eqs = 
        do (rigid,flex) <- partitionM (\eq -> compareHeads eq []) eqs
           if null rigid 
               then return eqs
               else massDecompose rigid
                      >>= simplify
                      >>= (\x -> return $ flex ++ x)

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f [] = return ([], [])
partitionM f (x:xs) = do
    res <- f x
    (as,bs) <- partitionM f xs
    return $ if res then (x : as,     bs)
                    else (    as, x : bs)

massDecompose l = M.lift $ concat <$> mapM (\(x:=:y) -> statefulDecompose x y) l

-- | returns true on rigid-rigid equations between terms in βη long normal form
--(since these are guaranteed to have heads that are either constants or
--variables), and false on flex-whatever equations (so you should orient
--before using) but also causes the computational branch to fail of there's
--a mismatch of rigid-rigid heads
compareHeads :: (HigherOrder f, MonadVar f m) => Equation f -> [AnyPig f] -> LogicT m Bool
compareHeads (x:=:y) bv = case (castLam x, castLam y) of
                         (Just (ExtLam (l :: f t1 -> f t1') Refl),Just (ExtLam (l' :: f t2 -> f t2') Refl)) -> do 
                              case (eqT :: Maybe (t1 :~: t2)) of
                                  Just Refl -> do lv <- M.lift $ fresh
                                                  compareHeads (l lv :=: l' lv) (AnyPig lv:bv)
                                  Nothing -> mzero
                         _ -> do (p1,_) <- guillotine x
                                 if freeVar p1 
                                    then return False
                                    else do (p2,_) <- guillotine y
                                            if p1 == p2 then return True
                                                        else mzero
    where freeVar ap@(AnyPig x) = isVar x && not (ap `elem` bv)

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
-- the left), this indeterministically returns the associated
-- substituitional equation. 
--
--bad behavior can be expected when given a rigid/rigid, flexible/flexible,
--or rigid/flexible equation.
generate :: (MonadVar f m, HigherOrder f) => Equation f -> LogicT m (Equation f)
generate ((x :: f a) :=: y) = --accumulator for projection terms
         do case (castLam x, castLam y) of
                (Just (ExtLam l Refl),Just (ExtLam l' Refl)) -> 
                    do fv <- M.lift fresh
                       generate $ (l fv) :=: (l' fv)
                (Nothing, Nothing) -> 
                    do (AnyPig (headX :: f t1), projterms) <- guillotine x
                       projvars <- M.lift $ toVars projterms
                       --on the next line, we pass in the projterms to give
                       --evidence of the types of the projvars, so that we
                       --can apply the projvars to appropriate terms before
                       --rebinding
                       let vbranches = map (project projvars) $ zip projvars projterms
                       let hbranch = imitate projvars (AnyPig y)
                       (AnyPig (newTerm :: f t5)) <- hbranch `mplus` foldr mplus mzero vbranches 
                       case eqT :: Maybe (t5 :~: t1) of
                           Just Refl -> return (headX:=:newTerm)
                           Nothing -> mzero

guillotine :: (HigherOrder f, Typeable a, Monad m) => f a -> m (AnyPig f, [AnyPig f])
guillotine x = basket (AnyPig x) []
            where basket (AnyPig x) pigs = case matchApp x of
                      Just (ExtApp h t) -> basket (AnyPig h) ((AnyPig t):pigs)
                      Nothing -> return (AnyPig x,pigs)

--XXX: this inserts some vacuous lambdas. This could be avoided by using
--`occurs sv` as a guard in reabstract, but it seems more efficient to just
--leave them in (though there's no perceptible difference either way)
statefulDecompose :: (HigherOrder f, Typeable a, MonadVar f m) => f a -> f a -> m [Equation f]
statefulDecompose a b = case (castLam a, castLam b) of
            (Just (ExtLam (f ::  f a -> f b) Refl), Just (ExtLam (f' :: f a' -> f b') Refl)) -> 
                case (eqT :: Maybe (a:~:a'), eqT :: Maybe (b:~:b')) of
                    (Just Refl, Just Refl) -> do sv <- fresh
                                                 decd <- statefulDecompose (f sv) (f' sv)
                                                 return (map (reabstract sv) decd)
                    _ -> return []
            (Nothing, Nothing) -> return $ recur a b []
    where recur :: (HigherOrder f, Typeable a, Typeable b) => f a -> f b -> [Equation f] -> [Equation f]
          recur a b terms = case (matchApp a, matchApp b) of
            (Just (ExtApp h (t :: f a)), Just (ExtApp h' (t' :: f a'))) -> 
                case eqT :: Maybe (a :~: a') of
                    Just Refl -> recur h h' ((t:=:t'):terms)
                    _ -> []
            _ -> terms
          reabstract sv (t:=:t') = lam (\x -> subst sv x t) :=: lam (\x -> subst sv x t')

--recursively performs a surgery on a term (either a projection term or the
--body of the rhs), eventually replacing every part of the term with an
--appropriate chunk of variables.
--
--Note that the projection term will not be of the same type as the return
--value. Hence, we need an AnyPig here.
project :: (MonadVar f m, HigherOrder f) => [AnyPig f] -> (AnyPig f,AnyPig f) -> LogicT m (AnyPig f)
project pvs (AnyPig (var :: f vt), AnyPig (term :: f tt)) = 
        case eqT :: Maybe (vt :~: tt) of
            Just Refl -> do pigbodies <- M.lift $ handleBodyAbs pvs var term []
                            projections <- M.lift $ mapM (bindAll (reverse pvs)) pigbodies
                            foldr mplus mzero (map return projections)
            Nothing -> error "var/term mismatch"

imitate :: (MonadVar f m, HigherOrder f) => [AnyPig f] -> AnyPig f -> LogicT m (AnyPig f)
imitate pvs (AnyPig term) 
    | isVar term = mzero
    | otherwise = 
        do body <- M.lift $ handleBodyApp pvs term
           imitation <- M.lift $ bindAll (reverse pvs) (AnyPig body)
           return imitation 

handleBodyApp :: (MonadVar f m, HigherOrder f, Typeable a) => [AnyPig f] -> f a -> m (f a)
handleBodyApp projvars term = case matchApp term of
   Nothing -> return term
   (Just (ExtApp h t)) -> do newInit <- handleBodyApp projvars h
                             freshArg <- genFreshArg projvars newInit
                             return $ newInit .$. freshArg

handleBodyAbs :: (MonadVar f m, HigherOrder f, Typeable a) 
    => [AnyPig f] -> f a -> f a -> [AnyPig f] ->  m [AnyPig f]
handleBodyAbs projvars var term acc = case castLam term of
   Nothing -> return (AnyPig var:acc)
   (Just (ExtLam f Refl)) -> do freshArg <- genFreshArg projvars term
                                handleBodyAbs projvars (var .$. freshArg) (f freshArg) (AnyPig var:acc)

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

genFreshArg :: (MonadVar f m, HigherOrder f, Typeable a) => 
    [AnyPig f] -> f (a -> b) -> m (f a)
genFreshArg projvars term =
        do (EveryPig head) <- freshPig 
           return $ attach head projvars
    where attach ::  (HigherOrder f, Typeable d) 
            => (forall c . Typeable c => f c) -> [AnyPig f] -> f d
          attach h  ((AnyPig v):vs) = attach (h .$. v) vs
          attach h [] = h

-- | solve a pattern-matching unification problem (specialized to matching
-- for efficiency)
huetmatch :: (HigherOrder f, MonadVar f m)
        => (forall a. f a -> Bool) --treat certain variables as constants
        -> [Equation f] --equations to be solved
        -> [Equation f] --accumulator for the substitution
        -> LogicT m [Equation f]
huetmatch varConst [] ss = return (reverse ss)
huetmatch varConst es ss = 
        do seqs <- simplify es
           case nub seqs of 
                []     -> return (reverse ss)
                (x:xs) -> do lnfx <- (M.lift . eqLMatch) x
                             genSub@(a:=:b) <- generate lnfx
                             let subbed = map (emapL (subst a b)) (x:xs) 
                                 --XXX: we only sub on LHS since we're matching
                             fresheqs <- mapM (M.lift . eqFreshen) subbed
                             huetmatch varConst (filter (not . trivial) fresheqs) (genSub:ss)
    where trivial (x:=:y) = x =* y

eqLMatch :: (MonadVar f m, HigherOrder f) => Equation f -> m (Equation f)
eqLMatch (x :=: y) = 
        case (castLam x, castLam y) of
             (Nothing, Nothing) -> 
                return (x :=: y)
             (Nothing, Just (ExtLam f Refl)) -> 
                do v <- fresh 
                   (x':=: y') <- eqLMatch (x .$. v :=: f v)
                   return $ (lam $ \z -> subst v z x') :=: (lam $ \z -> subst v z y')
             (Just (ExtLam f Refl), Nothing) -> 
                do v <- fresh 
                   (x':=: y') <- eqLMatch (f v :=: (y .$. v))
                   return $ 
                        (lam $ \z -> subst v z x') :=:
                        (lam $ \z -> subst v z y') 
             (Just (ExtLam f Refl), Just (ExtLam f' Refl)) -> 
                do v <- fresh
                   (x':=:y') <- eqLMatch (f v :=: f' v)
                   return $ 
                        (lam $ \z -> subst v z x') :=:
                        (lam $ \z -> subst v z y') 
                   
eqFreshen :: (HigherOrder f, MonadVar f m) => Equation f -> m (Equation f)
eqFreshen ((x :: f a):=:y) =  do return (betaNormalizeByName x :=: y)

huetMatchSys :: (MonadVar f m, HigherOrder f) => (forall a. f a -> Bool) -> [Equation f] -> m [[Equation f]]
huetMatchSys varConst eqs = observeAllT (huetmatch varConst eqs [])
