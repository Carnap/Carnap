{-#LANGUAGE ScopedTypeVariables, InstanceSigs, ExplicitForAll, TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Core.Examples.ACUI (
    V, Set, VLang, Var, acuiParser,
    pattern VEmpty, pattern VUnion, pattern VSomeSet, pattern VSingelton,
    parseTerm, evalTerm
    --acuiDemo
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.ACUI
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.Combination
import Carnap.Core.Util
import qualified Data.Set as S
import Data.Type.Equality
import Data.Typeable
import Text.Parsec hiding (Empty)
import Text.Parsec.Expr
import Control.Monad.State

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

data Extra a where
    ConstUnFunc :: String -> Extra (Term V -> Term V)
    ConstBinFunc :: String -> Extra (Term V -> Term V -> Term V)

instance UniformlyEq Extra where
    (ConstUnFunc s)  =* (ConstUnFunc s')  = s == s'
    (ConstBinFunc s) =* (ConstBinFunc s') = s == s'
    _                =* _                 = False

instance Schematizable Extra where
    schematize (ConstUnFunc s) (x:_)    = s ++ "(" ++ x ++ ")"
    schematize (ConstBinFunc s) (x:y:_) = s ++ "(" ++ x ++ "," ++ y ++ ")"

instance Evaluable Extra where
    eval _ = error "don't do this, I too lazy to implement this"

instance FirstOrderLex Extra

type VLex = (Function Set :|: Var :|: SubstitutionalVariable :|: Function Extra :|: EndLang)

type VLang = FixLang VLex

type VTerm = VLang (Term V)

pattern VEmpty = Fx1 (Function Empty AZero)
pattern VSomeSet s = Fx2 (SomeSet s)
pattern VSingelton x = Fx1 (Function Singleton AOne) :!$: x
pattern VUnion x y = Fx1 (Function Union ATwo) :!$: x :!$: y
pattern SV n = Fx3 (SubVar n)
pattern VUnFunc s x = Fx4 (Function (ConstUnFunc s) AOne) :!$: x
pattern VBinFunc s x y = Fx4 (Function (ConstBinFunc s) ATwo) :!$: x :!$: y

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

--This is just a place holder until we define things compositionally
data VLangLabel = VExtra
                | VSet
    deriving(Eq, Ord, Show)

instance Combineable VLang VLangLabel where
    getLabel VEmpty           = VSet
    getLabel (VSingelton _)   = VSet
    getLabel (VUnion _ _)     = VSet
    getLabel (VUnFunc _ _)    = VExtra
    getLabel (VBinFunc _ _ _) = VExtra

    getAlgo VSet = undefined
    getAlgo VExtra = undefined

    replaceChild (VSingelton _)   pig _ = VSingelton $ unEveryPig pig
    replaceChild (VUnion _ x)     pig 0 = VUnion (unEveryPig pig) x
    replaceChild (VUnion x _)     pig 1 = VUnion x (unEveryPig pig)
    replaceChild (VUnFunc s _)    pig _ = VUnFunc s (unEveryPig pig)
    replaceChild (VBinFunc s _ x) pig 0 = VBinFunc s (unEveryPig pig) x
    replaceChild (VBinFunc s x _) pig 1 = VBinFunc s x (unEveryPig pig)

--this could likely be defined just using generic things
--however in this case I'm just defining it directly
--more work will be needed to define this for all
--needed languages.
{--
instance FirstOrder VLang where
  isVar (SV _)       = True
  isVar (VSomeSet _) = True
  isVar _            = False

  sameHead VEmpty           VEmpty            = True
  sameHead (SV s)           (SV s')           = s == s'
  sameHead (VUnion _ _)     (VUnion _ _)      = True
  sameHead (VSingelton _)   (VSingelton _)    = True
  sameHead (VUnFunc s _)    (VUnFunc s' _)    = s == s'
  sameHead (VBinFunc s _ _) (VBinFunc s' _ _) = s == s'
  sameHead _                _                 = False

  decompose (VUnion x y)     (VUnion x' y')     = [x :=: x', y :=: y']
  decompose (VSingelton x)   (VSingelton y)     = [x :=: y]
  decompose (VUnFunc _ x)    (VUnFunc _ y)      = [x :=: y]
  decompose (VBinFunc _ x y) (VBinFunc _ x' y') = [x :=: x', y :=: y']
  decompose _              _              = []

  occurs (SV s)       (SV s')          = s == s'
  occurs (VSomeSet s) (VSomeSet s')    = s == s'
  occurs v            (VUnion x y)     = occurs v x || occurs v y
  occurs v            (VSingelton x)   = occurs v x
  occurs v            (VUnFunc s x)    = occurs v x
  occurs v            (VBinFunc s x y) = occurs v x || occurs v y

  --this is complicated and should be hidden from the user
  subst v new (VBinFunc s x y)     = VBinFunc s (subst v new x) (subst v new y)
  subst v new (VUnFunc s x)        = VUnFunc s (subst v new x)
  subst v new (VUnion x y)         = VUnion (subst v new x) (subst v new y)
  subst v new (VSingelton x)       = VSingelton (subst v new x)
  subst (VSomeSet s) new orign@(VSomeSet s')
      | s == s'                    = new
      | otherwise                  = orign

  --freshVars = map (\n -> EveryPig (SV n)) [1..]

--}

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
                           return $ VSingelton inner

unfuncParser :: (Monad m) => ParsecT String u m (VTerm)
unfuncParser = do c <- oneOf "fgjkl"
                  char '('
                  arg <- acuiParser
                  char ')'
                  return $ VUnFunc [c] arg

binfuncParser :: (Monad m) => ParsecT String u m (VTerm)
binfuncParser = do c <- oneOf "rhtqs"
                   char '('
                   arg1 <- acuiParser
                   char ','
                   arg2 <- acuiParser
                   char ')'
                   return $ VBinFunc [c] arg1 arg2

somesetParser :: (Monad m) => ParsecT String u m (VTerm)
somesetParser = do c <- oneOf "abcdexyz"
                   return $ VSomeSet [c]

subvarParser :: (Monad m) => ParsecT String u m (VTerm)
subvarParser = do n <- read <$> many1 digit
                  return $ SV n

acuiParser :: (Monad m) => ParsecT String u m (VTerm)
acuiParser = buildExpressionParser [[Infix (try parseUnion) AssocLeft]] subParser
    where subParser = try emptyParser <|>
                      try unfuncParser <|>
                      try binfuncParser <|>
                      try (singletonParser acuiParser) <|>
                      subvarParser <|>
                      somesetParser

instance Show (Equation VLang) where
    show (a :=: b) = schematize a [] ++ " = " ++ schematize b []

parseTerm s = let (Right term) = parse acuiParser "" s in term
evalTerm m = evalState m 0

{--
acuiDemo = do
  lhs <- getLine
  if lhs /= ""
    then do
      rhs <- getLine
      let t1 = parse acuiParser "left hand side" lhs
      let t2 = parse acuiParser "right hand side" rhs
      case (t1, t2) of
        (Left err, _) -> print err
        (_, Left err) -> print err
        (Right x, Right y) -> print $ evalState (acuiUnify x y) freshVars
      acuiDemo
    else return ()
--}
