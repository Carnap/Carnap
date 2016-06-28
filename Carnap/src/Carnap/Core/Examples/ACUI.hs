{-#LANGUAGE ScopedTypeVariables, InstanceSigs, ExplicitForAll, TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Core.Examples.ACUI (
    V, Set, VLang, Var,
    pattern VEmpty, pattern VUnion, pattern VSomeSet, pattern VSingleton
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.ACUI
import qualified Data.Set as S
import Data.Type.Equality
import Data.Typeable
import Text.Parsec hiding (Empty)
import Text.Parsec.Expr

--I really liked this example so I'm using it for testing
newtype VFix f = VFix (f (VFix f))
    deriving(Typeable)
type V = VFix S.Set

ev :: V
ev = VFix S.empty

sv :: V -> V
sv x = VFix (S.singleton x)

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
    Singleton :: Set (Term V -> Term V)
    Union :: Set (Term V -> Term V -> Term V)

instance UniformlyEq Set where
        Empty =* Empty = True
        Singleton =* Singleton = True
        Union =* Union = True
        _ =* _ = False

instance FirstOrderLex Set

instance Monad m => MaybeMonadVar Set m where
        maybeFresh = Nothing

instance Schematizable Set where
    schematize Singleton (x:_) = "{" ++ x ++ "}"
    schematize Empty  _        = "{}"
    schematize Union  (x:y:_)  = x ++ " ∪ " ++ y

instance Evaluable Set where
    eval Empty = Term ev
    eval Union = \(Term t) (Term t') -> Term (uv t t')
    eval Singleton = \(Term t) -> Term (sv t)

data Var lang a where
    SomeSet :: String -> Var lang (Term V)

instance UniformlyEq (Var lang) where
    (SomeSet x) =* (SomeSet y) = x == y

instance FirstOrderLex (Var lang) where
        isVarLex (SomeSet _) = True

instance Monad m => MaybeMonadVar (Var lang) m where
        maybeFresh = Nothing

instance Schematizable (Var lang) where
    schematize (SomeSet s) _ = s

instance Evaluable (Var lang) where
    eval _ = error "you are not allowed to do that silly"

type VLex = (Function Set :|: Var :|: SubstitutionalVariable :|: EndLang)

type VLang = FixLang VLex

type VTerm = VLang (Term V)

pattern VEmpty = Fx1 (Function Empty AZero)
pattern VSomeSet s = Fx2 (SomeSet s)
pattern VSingleton x = Fx1 (Function Singleton AOne) :!$: x
pattern VUnion x y = Fx1 (Function Union ATwo) :!$: x :!$: y
pattern SV n = Fx3 (SubVar n)

instance LangTypes1 VLex Term V

instance BoundVars VLex where
  subBoundVar = undefined

instance CopulaSchema VLang where
    appSchema x y e = schematize x (show y : e)
    lamSchema = error "how did you even do this?"
    liftSchema = error "should not print a lifted value"

instance Monoid (VLang (Term V)) where
    mempty = VEmpty
    mappend = VUnion

instance Eq (VLang a) where
    (==) = (=*)

instance ACUI VLang (Term V) where
    unfoldTerm (VUnion x y) = unfoldTerm x ++ unfoldTerm y
    unfoldTerm VEmpty       = []
    unfoldTerm leaf         = [leaf]

--this could likely be defined just using generic things
--however in this case I'm just defining it directly
--more work will be needed to define this for all
--needed languages.
-- instance FirstOrder VLang where
--   isVar (SV _)       = True
--   isVar (VSomeSet _) = True
--   isVar _            = False

--   sameHead VEmpty         VEmpty         = True
--   sameHead (SV s)         (SV s')        = s == s'
--   sameHead (VUnion _ _)   (VUnion _ _)   = True
--   sameHead (VSingleton _) (VSingleton _) = True
--   sameHead _              _              = False

--   decompose (VUnion x y)   (VUnion x' y') = [x :=: x', y :=: y']
--   decompose (VSingleton x) (VSingleton y) = [x :=: y]
--   decompose _              _              = []

--   occurs (SV s) (SV s')        = s == s'
--   occurs v      (VUnion x y)   = occurs v x || occurs v y
--   occurs v      (VSingleton x) = occurs v x

--   --this is complicated and should be hidden from the user
--   subst v new (VUnion x y)         = VUnion (subst v new x) (subst v new y)
--   subst v new (VSingleton x)       = VSingleton (subst v new x)
--   subst (VSomeSet s) new orign@(VSomeSet s')
--       | s == s'                    = new
--       | otherwise                  = orign

--   freshVars = map SV [1..]

parseUnion :: (Monad m) => ParsecT String u m (VTerm -> VTerm -> VTerm)
parseUnion = do spaces
                string "u"
                spaces
                return VUnion

emptyParser :: (Monad m) => ParsecT String u m (VTerm)
emptyParser = do string "{}"
                 return VEmpty

singletonParser recur = do char '{'
                           inner <- recur
                           char '}'
                           return $ VSingleton inner
                     
somesetParser :: (Monad m) => ParsecT String u m (VTerm)
somesetParser = do c <- oneOf "abcdefghijklmnopqrstuvwxyz"
                   return $ VSomeSet [c]

subvarParser :: (Monad m) => ParsecT String u m (VTerm)
subvarParser = do n <- read <$> many1 digit
                  return $ SV n

acuiParser :: (Monad m) => ParsecT String u m (VTerm)
acuiParser = buildExpressionParser [[Infix (try parseUnion) AssocLeft]] subParser
    where subParser = try emptyParser <|>
                      try (singletonParser acuiParser) <|>
                      subvarParser <|>
                      somesetParser 

