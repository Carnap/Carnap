{-#LANGUAGE ScopedTypeVariables, InstanceSigs, ExplicitForAll, TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Core.Examples.ACUI () where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.ACUI
import qualified Data.Set as S
import Data.Type.Equality
import Data.Typeable

--I really liked this example so I'm using it for testing
newtype VFix f = VFix (f (VFix f))
    deriving(Typeable)
type V = VFix S.Set

ev :: V
ev = VFix S.empty

uv :: V -> V -> V
uv (VFix x) (VFix y) = VFix $ S.union x y

instance Show V where
        show (VFix x) = show x

instance Eq V where
        (VFix x) == (VFix y) = x == y

instance Ord V where
        (VFix x) <= (VFix y) = x <= y

--I don't want to handle constants just yet
--So this language has no singeltons but that comes next
data Set a where
    Empty :: Set (Term V)
    Union :: Set (Term V -> Term V -> Term V)

instance Schematizable Set where
    schematize Empty  _       = "{}"
    schematize Union  (x:y:_) = x ++ " ∪ " ++ y

instance Evaluable Set where
    eval Empty = Term ev
    eval Union = \(Term t) (Term t') -> Term (uv t t')

data Var lang a where
    SomeSet :: Typeable a => String -> Var lang a

instance Schematizable (Var lang) where
    schematize (SomeSet s) _ = s

instance Evaluable (Var lang) where
    eval _ = error "you are not allowed to do that silly"

type VLang = FixLang (Function Set :|: Var :|: EndLang)

pattern VEmpty = Fx1 (Function Empty AZero)
pattern VSomeSet s = Fx2 (SomeSet s)
pattern VUnion x y = Fx1 (Function Union ATwo) :!$: x :!$: y

--this could likely be defined just using generic things
--however in this case I'm just defining it directly
--more work will be needed to define this for all
--needed languages.

instance FirstOrder VLang where
  isVar (VSomeSet _) = True

  sameHead VEmpty VEmpty              = True
  sameHead (VSomeSet s) (VSomeSet s') = s == s'
  sameHead (VUnion _ _) (VUnion _ _)  = True
  sameHead _            _             = False

  decompose (VUnion x y) (VUnion x' y') = [x :=: x', y :=: y']
  decompose _            _              = []

  occurs (VSomeSet s) (VSomeSet s') = s == s'
  occurs v            (VUnion x y)  = occurs v x || occurs v y

  --this is complicated and should be hidden from the user
  subst v new (VUnion x y)         = VUnion (subst v new x) (subst v new y)
  subst (VSomeSet s :: VLang a) new orign@(VSomeSet s' :: VLang b)
      | s == s'   = case eqT :: Maybe (a :~: b) of
                        Just Refl -> new
                        Nothing   -> orign
      | otherwise                  = orign
  subst _            _   orign     = orign

  freshVars = undefined
  --freshVars :: forall a. [VLang a] --this is complicated
  --freshVars = case eqT :: Maybe (a :~: Term V) of
    --  Just Refl -> map (VSomeSet . ("x" ++) . show) [(1 :: Int) ..]
--}
