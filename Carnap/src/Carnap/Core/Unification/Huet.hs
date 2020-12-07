{-#LANGUAGE ImpredicativeTypes, ScopedTypeVariables, FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Huet
where

import Carnap.Core.Util
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification 
import Data.Typeable
import Data.List
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Trans.Class as M

-- | simplfies a set of equations, returning a set of equations with the same
--set of solutions, but no rigid-rigid equations---or Nothing, in the case
--where the set of equations has no solutions.
simplify ::(HigherOrder f, MonadVar f (State Int)) => [Equation f] -> LogicT (State Int) [Equation f]
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

-- | ensures that a list of equations is oriented, by dropping flex-flex
-- equations, and reversing equations that have a rigid term on the left
orient [] = return []
orient ((x:=:y):eqs) =  do chx <- constHead x []
                           oeqs <- orient eqs
                           if chx then return $ (y:=:x):oeqs
                                  else do chy <- constHead y []
                                          if chy then return $ (x:=:y):oeqs
                                                 else return oeqs

-- | returns true on rigid-rigid equations between terms in βη long normal form
--(since these are guaranteed to have heads that are either constants or
--variables).
rigidRigid :: (HigherOrder f, MonadVar f (State Int))  => Equation f -> (State Int) Bool
rigidRigid (x:=:y) = (&&) <$> constHead x [] <*> constHead y []

constHead ::  (HigherOrder f, MonadVar f (State Int), Typeable a, EtaExpand f a) => f a -> [AnyPig f] -> State Int Bool
constHead x bv = case castLam x of
 (Just (ExtLam l _)) -> do lv <- fresh
                           constHead (l lv) ((AnyPig lv):bv)
 _ ->  do (h, _) <- guillotine x
          return $ not (freeVar h)
 where freeVar p@(AnyPig x) = isVar x && not (p `elem` bv)

abstractEq :: (MonadPlus m, HigherOrder f, MonadVar f (State Int)) => AnyPig f -> AnyPig f -> Equation f -> m (Equation f)
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
generate :: (MonadVar f (State Int), HigherOrder f) => Equation f -> LogicT (State Int) (Equation f,Equation f)
generate ((x :: f a) :=: y) = --accumulator for projection terms
         do case (castLam x, castLam y) of
                (Just (ExtLam l Refl),Just (ExtLam l' Refl)) -> 
                    do fv <- M.lift fresh
                       (eq, sub) <- generate $ (l fv) :=:  (l' fv)
                       eq' <-  abstractEq (AnyPig fv) (AnyPig fv) eq
                       return (eq', sub)
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
                       gappyX <- M.lift $ safesubst headX x
                       case eqT :: Maybe (t5 :~: t1) of
                           Just Refl -> return (gappyX newTerm :=:y,headX:=:newTerm)
                           Nothing -> mzero

guillotine :: (HigherOrder f, Monad m,Typeable a, MonadVar f (State Int), EtaExpand f a) => f a -> m (AnyPig f, [AnyPig f])
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
project :: (MonadVar f (State Int), HigherOrder f) => [AnyPig f] -> (AnyPig f,AnyPig f) ->  LogicT (State Int) (AnyPig f)
project pvs (AnyPig (var :: f vt), AnyPig (term :: f tt)) = 
        case eqT :: Maybe (vt :~: tt) of
            Just Refl -> do pigbodies <- M.lift $ handleBodyAbs pvs var term []
                            projections <- M.lift $ mapM (bindAll (reverse pvs)) pigbodies
                            foldr mplus mzero (map return projections)
            Nothing -> error "var/term mismatch"

imitate :: (MonadVar f (State Int), HigherOrder f) => [AnyPig f] -> AnyPig f ->  LogicT (State Int) (AnyPig f)
imitate pvs (AnyPig term) 
    | isVar term = mzero
    | otherwise = 
        do body <- M.lift $ handleBodyApp pvs term
           imitation <- M.lift $ bindAll (reverse pvs) (AnyPig body)
           return imitation 

handleBodyApp :: (MonadVar f (State Int), HigherOrder f, Typeable a) => [AnyPig f] -> f a ->  State Int (f a)
handleBodyApp projvars term = case matchApp term of
   Nothing -> return term
   (Just (ExtApp h t)) -> do newInit <- handleBodyApp projvars h
                             freshArg <- genFreshArg projvars newInit
                             return $ newInit .$. freshArg

handleBodyAbs :: (MonadVar f (State Int), HigherOrder f, EtaExpand f a, Typeable a) 
    => [AnyPig f] -> f a -> f a -> [AnyPig f] ->  State Int [AnyPig f]
handleBodyAbs projvars var term acc = case castLam term of
   Nothing -> return (AnyPig var:acc)
   (Just (ExtLam f Refl)) -> do freshArg <- genFreshArg projvars term
                                handleBodyAbs projvars (var .$. freshArg) (f freshArg) (AnyPig var:acc)

toVars :: (MonadVar f m) => [AnyPig f] -> m [AnyPig f]
toVars (AnyPig (x :: f t):xs) = do y :: f t <- fresh 
                                   tail <- toVars xs
                                   return (AnyPig y:tail)
toVars [] = return []

bindAll :: (HigherOrder f, MonadVar f (State Int)) => [AnyPig f] -> AnyPig f -> State Int (AnyPig f)
bindAll (AnyPig v :vs) (AnyPig body ) = 
            do f <- safesubst v body
               bindAll vs (AnyPig (lam f))
bindAll [] body = return body

--substitute f a in f b while avoiding collision of variables
safesubst :: (HigherOrder f, MonadVar f m, Typeable a, Typeable b) => f a -> f b -> m (f a -> f b)
safesubst (x :: f a) (y :: f b) = return $ \z -> subst x z y

genFreshArg :: (MonadVar f (State Int), EtaExpand f a, HigherOrder f, Typeable a) => 
    [AnyPig f] -> f (a -> b) -> State Int (f a)
genFreshArg projvars term =
        do (EveryPig head) <- freshPig 
           return $ attach head projvars
    where attach ::  (HigherOrder f, Typeable d, MonadVar f (State Int), EtaExpand f d) 
            => (forall c . (Typeable c, EtaExpand f c) => f c) -> [AnyPig f] -> f d
          attach h  ((AnyPig v):vs) = attach (h .$. v) vs
          attach h [] = h

--- | given x, y with no leading variables, this applies the generate rule
--to replace the old head of x with the new head

huetunify :: (HigherOrder f, MonadVar f (State Int))
        => (forall a. f a -> Bool) --treat certain variables as constants
        -> [Equation f] --equations to be solved
        -> [Equation f] --accumulator for the substitution
        -> LogicT (State Int) [Equation f]
huetunify varConst [] ss = return (reverse ss)
huetunify varConst es ss = 
        do seqs <- simplify es
           case nub seqs of 
                []     -> return (reverse ss)
                (x:xs) -> do lnfx <- (M.lift . eqLMatch) x
                             (genEq, genSub@(a:=:b)) <- generate lnfx
                             let subbed = mapAll (subst a b) (genEq:xs)
                             lnfeqs <- mapM (M.lift . eqLNF) subbed
                             huetunify varConst (filter (not . trivial) lnfeqs) (genSub:ss)
    where trivial (x:=:y) = x =* y

huetunify' :: (HigherOrder f, MonadVar f (State Int))
        => (forall a. f a -> Bool) --treat certain variables as constants
        -> [Equation f] --equations to be solved
        -> [Equation f] --accumulator for the substitution
        -> Int
        -> LogicT (State Int) ([Equation f],[Equation f])
huetunify' varConst es ss 0 = return (es,reverse ss)
huetunify' varConst es ss n = 
        do seqs <- simplify es
           case nub seqs of 
                []     -> return (es,reverse ss)
                (x:xs) -> do lnfx <- (M.lift . eqLMatch) x
                             (genEq, genSub@(a:=:b)) <- generate lnfx
                             let subbed = mapAll (subst a b) (genEq:xs)
                             lnfeqs <- mapM (M.lift . eqLNF) subbed
                             huetunify' varConst (filter (not . trivial) lnfeqs) (genSub:ss) (n-1)
    where trivial (x:=:y) = x =* y

eqLMatch :: (MonadVar f (State Int), HigherOrder f) => Equation f -> (State Int) (Equation f)
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
                   
eqLNF :: (HigherOrder f, MonadVar f (State Int)) => Equation f -> (State Int) (Equation f)
eqLNF ((x :: f a):=:y) =  do x' <- toLNF x
                             y' <- toLNF y
                             return (x':=:y')

eqBNF (x:=:y) = do x' <- toBNF x
                   y' <- toBNF y
                   return (x':=:y')

huetUnifySys :: (MonadVar f (State Int), HigherOrder f) => (forall a. f a -> Bool) -> [Equation f] -> (State Int) [[Equation f]]
huetUnifySys varConst eqs = observeAllT (huetunify varConst eqs [])
