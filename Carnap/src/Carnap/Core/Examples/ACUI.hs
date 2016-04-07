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
    SomeSet :: String -> Var lang (Term V)

instance Schematizable (Var lang) where
    schematize (SomeSet s) _ = s

instance Evaluable (Var lang) where
    eval _ = error "you are not allowed to do that silly"

type VLang = FixLang (Function Set :|: Var :|: EndLang)

pattern VEmpty = Fx1 (Function Empty AZero)
pattern VSomeSet s = Fx2 (SomeSet s)
pattern VUnion x y = Fx1 (Function Union ATwo) :!$: x :!$: y

instance LangTypes (Function Set :|: Var :|: EndLang) Term V Term V

instance BoundVars (Function Set :|: Var :|: EndLang) where
  getBoundVar = undefined
  subBoundVar = undefined

instance CopulaSchema VLang where
    appSchema x y e = schematize x (show y : e)
    lamSchema = error "how did you even do this?"
    liftSchema = error "should not print a lifted value"

instance Monoid (VLang (Term V)) where
    mempty = VEmpty
    mappend = VUnion

instance CanonicalForm (VLang a) where
    canonical = id

--this could likely be defined just using generic things
--however in this case I'm just defining it directly
--more work will be needed to define this for all
--needed languages.
instance FirstOrder VLang where
  isVar (SV _)       = True
  isVar (VSomeSet _) = True
  isVar _            = False

  sameHead VEmpty VEmpty              = True
  sameHead (SV s)       (SV s')       = s == s'
  sameHead (VUnion _ _) (VUnion _ _)  = True
  sameHead _            _             = False

  decompose (VUnion x y) (VUnion x' y') = [x :=: x', y :=: y']
  decompose _            _              = []

  occurs (SV s) (SV s')      = s == s'
  occurs v      (VUnion x y) = occurs v x || occurs v y

  --this is complicated and should be hidden from the user
  subst v new (VUnion x y)         = VUnion (subst v new x) (subst v new y)
  subst (VSomeSet s) new orign@(VSomeSet s')
      | s == s'                    = new
      | otherwise                  = orign

  --freshVars = undefined
  freshVars = map SV [1..]
  --freshVars :: forall a. [VLang a] --this is complicated
  --freshVars = case eqT :: Maybe (a :~: Term V) of
    --  Just Refl -> map (VSomeSet . ("x" ++) . show) [(1 :: Int) ..]
--}
