{-#LANGUAGE ImpredicativeTypes, ScopedTypeVariables, FunctionalDependencies, TypeFamilies, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, GADTs, KindSignatures, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}

module Carnap.Core.Unification.Huet
        ( 
        )
    where

import Carnap.Core.Util
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification 
import Data.Typeable
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Trans.Class as M

-- | simplfies a set of equations, returning a set of equations with the same
--set of solutions, but no rigid-rigid equations---or Nothing, in the case
--where the set of equations has no solutions.
simplify eqs = 
    case filter rigidRigid eqs of
        [] -> Just eqs
        rr -> do failCheck rr 
                 >>= massDecompose 
                 >>= simplify
                 >>= (\x -> return $ (filter (not . rigidRigid) eqs) ++ x)
    where failCheck l = if and (map (\(x:=:y) -> sameHead x y) l) 
                           then Just l
                           else Nothing
          massDecompose l = Just $ concat $ map (\(x:=:y) -> decompose x y) l

-- | returns true on rigid-rigid equations between terms in βη long normal form
--(since these are guaranteed to have heads that are either constants or
--variables).

rigidRigid :: HigherOrder f => Equation f -> Bool
rigidRigid (x:=:y) = acc x y []
    where acc ::  (HigherOrder f, Typeable a) => f a -> f a -> [AnyPig f] -> Bool
          acc x y bv = case (castLam x, castLam y) of
           (Just (ExtLam l Refl), Just (ExtLam l' Refl)) -> acc (toBody l) (toBody l') (pigLamb l:pigLamb l': bv)
           _ -> case (matchApp x,matchApp y) of
                    (Just (ExtApp h _), Just (ExtApp h' _)) -> 
                        not (freeVar (AnyPig h) || freeVar (AnyPig h'))
                    _ -> False
           where freeVar p@(AnyPig x) = isVar x && not (p `elem` bv)

toBody l = l .$. getLamVar l

pigLamb :: (HigherOrder f, Typeable a) => f (a -> b) -> AnyPig f
pigLamb = AnyPig . getLamVar
       
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
generate :: (MonadVar f m, HigherOrder f) => Equation f -> [AnyPig f] -> LogicT m (Equation f,Equation f)
generate ((x :: f t1):=: y ) projterms = --accumulator for projection terms
         do case (castLam x, castLam y) of
                (Just (ExtLam l Refl),Just (ExtLam l' Refl)) -> 
                    do fv <- M.lift fresh
                       fv' <- M.lift fresh
                       (eq, sub) <- generate ((l .$. fv) :=:  (l' .$. fv')) projterms
                       let (Just eq') = abstractEq (AnyPig fv) (AnyPig fv') eq
                       return (eq', sub)
                (Nothing, Nothing) -> 
                    case (matchApp x, matchApp y) of
                        (Just (ExtApp (h :: f (t2-> t1)) (t :: f t2)), 
                         Just (ExtApp (h' :: f (t3->t1 )) (t':: f t3))) -> 
                            case eqT :: Maybe (t2 :~: t3) of
                                Just Refl -> 
                                    do (((z::f t4):=:w), sub) <- generate (h:=:h') ((AnyPig t):projterms)
                                       case eqT :: Maybe (t4 :~: (t3 -> t1)) of
                                           Just Refl -> 
                                                do let eq' = (z .$. t) :=: (w .$. t')
                                                   return (eq',sub)
                                           Nothing -> mzero
                                _ -> mzero
                        (Nothing,Nothing) -> do let vbranches = map (vbranch x) projterms
                                                let hbranch = M.lift $ imitate projterms x
                                                (newTerm :: f t5) <- foldr mplus hbranch vbranches
                                                case eqT :: Maybe (t5 :~: t1) of
                                                    Just Refl -> return (newTerm:=:y,x:=:newTerm)
                                                    Nothing -> mzero
    where vbranch :: (Typeable a, MonadVar f m) =>  f a -> AnyPig f -> LogicT m (f a)
          vbranch (x :: f a) (AnyPig (p :: f b)) = 
            case eqT :: Maybe (a :~: b) of
                Just Refl -> M.lift $ project projterms p
                Nothing -> mzero
                

--recursively performs a surgery on a projection term, eventually replacing every part
--of the term with an appropriate chunk of variables.
project :: (MonadVar f m, HigherOrder f, Typeable a) => [AnyPig f] -> f a ->  m (f a)
project projterms (term :: f t1) = 
        case matchApp term of
           Nothing -> return term
           (Just (ExtApp h t)) -> do newInit <- project projterms h
                                     freshArg <- genFreshArg projterms newInit
                                     return $ newInit .$. freshArg

genFreshArg :: (MonadVar f m, HigherOrder f) => [AnyPig f] -> f (a -> b) -> m (f a)
genFreshArg = undefined

-- rebuilds a term from just the head and the projection terms
imitate :: (MonadVar f m, HigherOrder f) => [AnyPig f] -> f a ->  m (f a)
imitate = undefined

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

