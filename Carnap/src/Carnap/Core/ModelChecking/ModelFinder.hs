{-#LANGUAGE ScopedTypeVariables, InstanceSigs, ExplicitForAll, TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}

module Carnap.Core.ModelChecking.ModelFinder (
  Set(Set), Fin(FSucc, FZero), MTerm(), MLang(),
  Domain, showElement, enumerateNames, enumerateValues,
  forAll, forSome, (.&.), (.|.), (.->.), subset,
  (.=.), (.$.), suchThat, union, inter, cross,
  enumTerms, set
) where

import Control.Monad.State
import Data.Typeable
import Data.Maybe
import qualified Data.List as List
import Carnap.Core.ModelChecking.SAT
import Carnap.Core.Util
import Carnap.Languages.Util.LanguageClasses

--------------------------------------------------------------------------------
-- 1. Framework Setup
--------------------------------------------------------------------------------

--we a type to denote a set of things
newtype Set a = Set [a]
    deriving(Ord, Eq, Show)

--we need a way to name free sets
data SetName nm t where
    SetName :: (Show nm, Eq nm, Typeable t, Domain t) => nm -> SetName nm t

--we need a way to name elements of the domains
data TermName t where
    DomainName :: Domain t => Int -> TermName t
    DomainPairName :: (Domain t, Domain t') => TermName t -> TermName t' -> TermName (t, t')

instance Eq (TermName t) where
    (DomainName i) == (DomainName i') = i == i'
    (DomainPairName n1 n2) == (DomainPairName n1' n2') = n1 == n1' && n2 == n2'

--currentlly we only have 1 base predicate that gets converted to SAT
data Pred nm where
    PIn :: TermName t -> SetName nm t -> Pred nm

eqSetName (SetName i) (SetName j) = i == j
eqTermName :: TermName t -> TermName t' -> Bool
eqTermName (DomainName i)         (DomainName j)           = i == j
eqTermName (DomainPairName t1 t2) (DomainPairName t1' t2') = eqTermName t1 t1' && eqTermName t2 t2'
eqTermName _                      _                        = False

instance Eq (Pred nm) where
    (PIn tn sn) == (PIn tn' sn') = eqTermName tn tn' && eqSetName sn sn'

instance Show (Pred nm) where
    show (PIn tn (SetName i)) = showElement tn ++ " ∈ S_" ++ show i

--instance Show Pred where
  --  show (PIn t s) = show t ++ " ∈ " ++ show s

--------------------------------------------------------------------------------
-- 2. SAT problem setup
--------------------------------------------------------------------------------

--a type to represent boolean formulas over basic Preds
data Sat nm = SPred (Pred nm)
            | SAnd (Sat nm) (Sat nm)
            | SOr (Sat nm) (Sat nm)
            | SNot (Sat nm)
            | SBool Bool
    deriving(Eq, Show)

sImpl x y = SOr (SNot x) y

type Clause a = [Literal a]
type CNF a = [Clause a]
--types, function

sat2CNF :: Sat nm -> State Int (CNF (Either (Pred nm) Int))
sat2CNF (SNot (SAnd x y)) = sat2CNF (SOr (SNot x) (SNot y))
sat2CNF (SNot (SOr x y))  = sat2CNF (SAnd (SNot x) (SNot y))
sat2CNF (SNot (SNot x))   = sat2CNF x
sat2CNF (SNot (SBool b))  = sat2CNF $ SBool (not b)
sat2CNF (SNot (SPred p))  = return [[LNeg . Left $ p]]
sat2CNF (SPred p)         = return [[LPos . Left $ p]]
sat2CNF (SBool True)      = return []   -- the lack of constraints is true
sat2CNF (SBool False)     = return [[]] -- the lack of allowences is false
sat2CNF (SAnd x y)        = do
    cx <- sat2CNF x
    cy <- sat2CNF y
    return $ cx ++ cy
sat2CNF (SOr x y)         = do --now for the complicated case
    z <- get
    put (z + 1)
    let zl = Right z
    xs <- sat2CNF x
    ys <- sat2CNF y
    return $ (map ((LPos zl):) xs) ++ (map ((LNeg zl):) ys)

--------------------------------------------------------------------------------
-- 3. Language definition
--------------------------------------------------------------------------------

--the terms of our logic
data MTerm nm t where
    MSingelton :: Domain t => TermName t -> MTerm nm (Set t)
    MSetName :: Domain t => SetName nm t -> MTerm nm (Set t)
    MComp :: Domain t => (MTerm nm (Set t) -> MLang nm) -> MTerm nm (Set t)
    MJoin :: (Domain a, Domain b, Domain c) => MTerm nm (Set (a, b)) -> MTerm nm (Set (b, c)) -> MTerm nm (Set (a, c))
    MImage :: (Domain a, Domain b) => MTerm nm (Set (a, b)) -> MTerm nm (Set a) -> MTerm nm (Set b)
    MCross :: (Domain a, Domain b) => MTerm nm (Set a) -> MTerm nm (Set b) -> MTerm nm (Set (a, b))

--the propostions of our logic
data MLang nm where
    MForall :: Domain t => (MTerm nm (Set t) -> MLang nm) -> MLang nm
    MExists :: Domain t => (MTerm nm (Set t) -> MLang nm) -> MLang nm
    MAnd :: MLang nm -> MLang nm -> MLang nm
    MOr :: MLang nm -> MLang nm -> MLang nm
    MNot :: MLang nm -> MLang nm
    MSubset :: Domain t => MTerm nm (Set t) -> MTerm nm (Set t) -> MLang nm

--all the values strictly less than a certian natural number as specified by
--a type
data Fin :: Nat -> * where
    FZero :: Fin (Succ n)
    FSucc :: Fin n -> Fin (Succ n)

toInt :: Fin n -> Int
toInt (FSucc n) = 1 + toInt n
toInt FZero     = 0

instance Show (Fin n) where
    show n = show (toInt n)

instance Eq (Fin t) where
    FZero     == FZero      = True
    (FSucc n) == (FSucc n') = n == n'
    _         == _          = False

class Eq t => Domain t where
    showElement :: TermName t -> String
    enumerateValues :: [t]
    enumerateNames :: [TermName t]

instance (Domain a, Domain b) => Domain (a, b) where
    showElement (DomainName idx) = showElement $ (enumerateNames :: [TermName (a, b)]) !! idx
    showElement (DomainPairName an bn) = "(" ++ showElement an ++ ", " ++ showElement bn ++ ")"
    enumerateValues = [(a, b) | a <- enumerateValues, b <- enumerateValues]
    enumerateNames = [DomainPairName na nb | na <- enumerateNames, nb <- enumerateNames]

instance Domain (Fin Zero) where
    showElement = undefined
    enumerateValues = []
    enumerateNames = []

instance Domain (Fin n) => Domain (Fin (Succ n)) where
    showElement (DomainName idx) = show $ (enumerateValues :: [Fin (Succ n)]) !! idx
    enumerateValues = FZero : map FSucc (enumerateValues :: [Fin n])
    enumerateNames = map DomainName [0..length (enumerateValues :: [Fin (Succ n)]) - 1]

instance BooleanLanguage (MLang nm) where
    lneg = MNot
    land = MAnd
    lor = MOr
    lif x y = (lneg x) .|. y
    liff x y = (x .=>. y) ./\. (y .=>. x)

mnot :: MLang nm -> MLang nm
mnot = lneg

set :: (Typeable t, Domain t) => String -> MTerm String (Set t)
set s = MSetName (SetName s)

(.->.) :: MLang nm -> MLang nm -> MLang nm
(.->.) = lif
(.&.) :: MLang nm -> MLang nm -> MLang nm
(.&.) = land
(.|.) :: MLang nm -> MLang nm -> MLang nm
(.|.) = lor

--helpers to make using the language easier
forAll :: Domain t => (MTerm nm (Set t) -> MLang nm) -> MLang nm
forAll = MForall
forSome :: Domain t => (MTerm nm (Set t) -> MLang nm) -> MLang nm
forSome = MExists
subset :: Domain t => (MTerm nm (Set t)) -> (MTerm nm (Set t)) -> MLang nm
subset = MSubset
(.=.) a b = (a `subset` b) .&. (b `subset` a)

--helpers for working in the terms
(.$.) :: (Domain a, Domain b) => MTerm nm (Set (a, b)) -> MTerm nm (Set a) -> MTerm nm (Set b)
(.$.) = MImage
suchThat :: Domain t => (MTerm nm (Set t) -> MLang nm) -> MTerm nm (Set t)
suchThat = MComp
x `union` y = suchThat (\z -> (z `subset` x) .|. (z `subset` y))
x `inter` y = suchThat (\z -> (z `subset` x) .&. (z `subset` y))
cross :: (Domain a, Domain b) => MTerm nm (Set a) -> MTerm nm (Set b) -> MTerm nm (Set (a, b))
cross = MCross

--------------------------------------------------------------------------------
-- 4. Conversion to boolean SAT
--------------------------------------------------------------------------------

toSat :: MLang nm -> Sat nm
toSat (MForall (f :: MTerm nm (Set t) -> MLang nm)) = foldr SAnd (SBool True) preds
    where preds = map (toSat . f . MSingelton) (enumerateNames :: [TermName t])
toSat (MExists (f :: MTerm nm (Set t) -> MLang nm)) = foldr SOr (SBool False) preds
    where preds = map (toSat . f . MSingelton) (enumerateNames :: [TermName t])
toSat (MAnd x y) = SAnd (toSat x) (toSat y)
toSat (MOr x y) = SOr (toSat x) (toSat y)
toSat (MNot x) = SNot (toSat x)
toSat (MSubset (a :: MTerm nm (Set t)) b) = foldr SAnd (SBool True ) preds
    where names = enumerateNames :: [TermName t]
          preds = map (\n -> (inToPred n a) `sImpl` (inToPred n b)) names

inToPred :: Domain t => TermName t -> MTerm nm (Set t) -> Sat nm
inToPred name (MSingelton name')            = SBool (name == name')
inToPred name (MSetName setname)            = SPred $ PIn name setname
inToPred name (MComp t)                     = toSat . t . MSingelton $ name
inToPred (DomainPairName na nc) (MJoin f g) = toSat check
    where a = MSingelton na
          c = MSingelton nc
          check = forSome (\b -> ((a `cross` b) `subset` f) .&.
                                 ((b `cross` c) `subset` g))
inToPred name (MImage f a) = toSat check
    where check = forSome (\x -> (x `subset` a) .&. ((a `cross` b) `subset` f))
          b = MSingelton name
inToPred (DomainPairName na nb) (MCross a b) = SAnd (inToPred na a) (inToPred nb b)

--------------------------------------------------------------------------------
-- 5. Conversion back to values
--------------------------------------------------------------------------------

type Model a = [Literal a]

getValue :: forall t. TermName t -> t
getValue (DomainName idx) = (enumerateValues :: [t]) !! idx
getValue (DomainPairName n1 n2) = (getValue n1, getValue n2)

pred2set :: forall nm t. SetName nm t -> Pred nm -> [t]
pred2set (SetName j) (PIn tname ((SetName i) :: SetName nm t')) = case eqT :: Maybe (t :~: t') of
    Just Refl -> if i == j then [getValue tname] else []
    Nothing   -> []

maybePos (LPos v) = Just v
maybePos _        = Nothing
maybeLeft (Left v) = Just v
maybeLeft _        = Nothing

satModel2set :: Model (Either (Pred nm) Int) -> SetName nm t -> [t]
satModel2set model set = mapMaybe (maybePos >=> maybeLeft) model >>= (pred2set set)

evalForm :: Model (Either (Pred nm) Int) -> MLang nm -> Bool
evalForm model (MForall f)   = all (evalForm model . f . MSingelton) enumerateNames
evalForm model (MExists f)   = any (evalForm model . f . MSingelton) enumerateNames
evalForm model (MAnd a b)    = (evalForm model a) && (evalForm model b)
evalForm model (MOr a b)     = (evalForm model a) || (evalForm model b)
evalForm model (MNot a)      = not $ evalForm model a
evalForm model (MSubset a b) = null (aSet List.\\ bSet)
    where (Set aSet) = evalTerm model a
          (Set bSet) = evalTerm model b

formNames :: MLang nm -> [Pred nm]
formNames (MForall (f :: MTerm nm (Set t) -> MLang nm)) = formNames $ f (MSingelton name)
    where name = head (enumerateNames :: [TermName t])
formNames (MExists (f :: MTerm nm (Set t) -> MLang nm)) = formNames $ f (MSingelton name)
    where name = head (enumerateNames :: [TermName t])
formNames (MAnd a b) = formNames a ++ formNames b
formNames (MOr a b) = formNames a ++ formNames b
formNames (MNot a) = formNames a
formNames (MSubset a b) = setPreds a ++ setPreds b

evalTerm :: Model (Either (Pred nm) Int) -> MTerm nm t -> t
evalTerm model (MSingelton n) = Set $ [getValue n]
evalTerm model (MSetName n)   = Set $ satModel2set model n
evalTerm model (MComp f)      = Set $ map getValue names
    where names = filter (evalForm model . f . MSingelton) enumerateNames
evalTerm model (MJoin f g)    = Set [(a, c) | (a, b1) <- fs, (b2, c) <- gs, b1 == b2]
    where (Set fs) = evalTerm model f
          (Set gs) = evalTerm model g
evalTerm model (MImage f a)   = Set [b | a <- as, (a', b) <- fs, a == a']
    where (Set as) = evalTerm model a
          (Set fs) = evalTerm model f
evalTerm model (MCross a b)   = Set [(a, b) | a <- as, b <- bs]
    where (Set as) = evalTerm model a
          (Set bs) = evalTerm model b

setPreds :: MTerm nm t -> [Pred nm]
setPreds (MSetName (s :: SetName nm t))  = [PIn n s | n <- names]
    where names = enumerateNames :: [TermName t]
setPreds (MSingelton _)               = []
setPreds (MComp (f :: MTerm nm (Set t) -> MLang nm)) = formNames $ f (MSingelton name)
    where name = head (enumerateNames :: [TermName t])
setPreds (MJoin f g) = setPreds f ++ setPreds g
setPreds (MImage f a) = setPreds f ++ setPreds a
setPreds (MCross a b) = setPreds a ++ setPreds b

enumModels l = enumerate [] . search . makeProblemWith names . conv . toSat $ l
    where conv st = evalState (sat2CNF st) 1
          names = map Left (formNames l)

enumTerms :: forall nm t. MLang nm -> MTerm nm t -> [t]
enumTerms l t = map (\m -> evalTerm m t) (enumerate [] . search . makeProblemWith names . conv . toSat $ l)
    where conv :: Sat nm -> CNF (Either (Pred nm) Int)
          conv st = evalState (sat2CNF st) 1
          names = map Left (setPreds t ++ formNames l)

--example stuff for testing
bn = SetName 0 :: SetName Int (Fin (Succ (Succ Zero))) --this is a subset of the set {0, 1}
an = SetName 1 :: SetName Int (Fin (Succ (Succ Zero))) --this is a subset of the set {0, 1}
a = MSetName an
b = MSetName bn
