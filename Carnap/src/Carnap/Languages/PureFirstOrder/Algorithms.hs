{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.PureFirstOrder.Algorithms (
) where

import Carnap.Languages.PureFirstOrder.Syntax
import Control.Lens.Plated (plate,universe)
import Control.Lens.Setter (over)
import Control.Lens.Fold (toListOf)
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.Util.GenericConnectives
import Carnap.Core.Data.Util
import Data.Set (fromList, size)

--------------------------------------------------------
--Truth Functional Expansions
--------------------------------------------------------

--Counts total number n of monadic predicates. A counterexample is guaranteed
--if we use an expansion with 2^n constant symbols.
predicateCount :: PureMFOLForm -> Int
predicateCount phi = size . fromList $ foldl addPred [] (universe phi)
    where addPred :: [Int] -> PureMFOLForm -> [Int]
          addPred xs (PMPred n :!!$: _) = n:xs
          addPred xs _ = xs

--get maximum constant in given formula, in order to find new constants
maxconstant :: PureMFOLForm -> Int
maxconstant phi = foldl max 0 (map toIndex $ toListOf termsOf phi)
    where toIndex :: PureMFOLTerm -> Int
          toIndex (PC n) = n
          toIndex _ = 0

expandOver :: [PureMFOLTerm] -> PureMFOLForm -> PureMFOLForm
expandOver (c:cs) (PQuant (All _) :!!$: LLam g) = foldl (:&:) (g c) (map g cs)
expandOver (c:cs) (PQuant (Some _) :!!$: LLam g) =  foldl (:||:) (g c) (map g cs)
expandOver _ phi = phi

--`phi` is valid iff `toTruthFuncExpansion phi` is tautologically valid
toTruthFuncExpansion phi = recur phi
        where cnum = 2 ^ (predicateCount phi)
              cstream = (map PC [1 ..]) :: [PureMFOLTerm]
              consts = take cnum $ drop (maxconstant phi) cstream
              expand = expandOver consts
              recur phi = (over plate recur) $ expand phi

--------------------------------------------------------
--Tableaux Generation
--------------------------------------------------------
