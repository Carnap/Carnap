{-#LANGUAGE GADTs, TypeOperators, ScopedTypeVariables, ExplicitForAll, RankNTypes, MultiParamTypeClasses, FlexibleContexts, PatternSynonyms #-}

module Carnap.Core.Unification.AU (AU(..), auMatchSys) where

import Carnap.Core.Data.Classes
import Carnap.Core.ModelChecking.SAT
import Carnap.Core.Unification.Unification
import Carnap.Core.Util
import Data.Typeable
import Control.Monad.Logic
import Control.Monad.Trans.Class as M
import Data.List
import Data.Function
import Data.Proxy

class FirstOrder f => AU f where
  isAU :: f a -> Bool 
  isIdAU :: f a -> Bool 
  auId :: Typeable a => Proxy a -> f a
  auOp :: f a -> f a -> f a
  auUnfold :: f a -> [f a]

asVar varConst x = isVar x && not (varConst x)

--runs the matching after conversion to lists, with an accumulator
matchAccum :: (MonadVar f m, AU f, Typeable a, EtaExpand f a, UniformlyEq f) => (forall a. f a -> Bool) -> [f a] -> [f a] -> [Equation f] -> LogicT m [Equation f]
matchAccum varConst [] [] acc = return acc
matchAccum varConst [] (rh:rt) acc | asVar varConst rh = matchAccum varConst [] (filter (\t -> not $ t =* rh) rt) ((rh :=: auId Proxy):acc) --if RHS head is a variable, send it to the unit
matchAccum varConst (lh:lt) (rh:rt) acc | asVar varConst rh = freshBranch `mplus` unitBranch
    where freshBranch = do v <- M.lift fresh
                           let rep = lh `auOp` v
                           matchAccum varConst lt (v: map (applySub [rh :=: rep]) rt) ((rh :=: rep):acc) 
          unitBranch = matchAccum varConst (lh:lt) (filter (\t -> not $ t =* rh) rt) ((rh :=: auId Proxy):acc)
matchAccum varConst (lh:ht) (rh:rt) acc | lh =* rh = matchAccum varConst ht rt acc
matchAccum varConst [] (rh:rt) acc = mzero -- if RHS head is nonvariable, terminate branch
matchAccum varConst (lh:lt) [] acc = mzero -- if LHS is longer than RHS, terminate
matchAccum varConst (lh:ht) (rh:rt) acc = mzero -- if LHS and RHS heads are distinct nonvariable, terminate

auMatch :: (MonadVar f m, AU f, Typeable a, EtaExpand f a, UniformlyEq f) => (forall a. f a -> Bool) -> f a -> f a -> LogicT m [Equation f]
auMatch varConst a b = matchAccum varConst (auUnfold a) (auUnfold b) []

auMatchSys :: (MonadVar f m, AU f, UniformlyEq f) => (forall a. f a -> Bool) -> [Equation f] -> m [[Equation f]]
auMatchSys varConst eqs = observeAllT (prematch eqs)
    where prematch ((a :=: b):eqs) = do 
                    sub <- auMatch varConst a b
                    let eqs' = mapAll (applySub sub) eqs
                    sub' <- prematch eqs'
                    return $ sub ++ sub'
          prematch [] = return []
