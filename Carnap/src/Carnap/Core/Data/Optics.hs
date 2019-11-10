{-#LANGUAGE  UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, GADTs, PolyKinds, TypeOperators, RankNTypes, FlexibleContexts, ScopedTypeVariables  #-}
module Carnap.Core.Data.Optics(
  RelabelVars(..),  PrismLink(..), (:<:)(..), ReLex(..), unaryOpPrismOn, unaryOpPrism, binaryOpPrismOn, binaryOpPrism, genChildren, PrismSubstitutionalVariable(..), flipt, relexIso
) where

import Carnap.Core.Data.Types
import Carnap.Core.Unification.Unification
import Control.Lens(Plated(..), Lens'(..), lens, Prism'(..), prism', preview, Iso'(..), iso, review, Traversal'(..),transformM, Iso,iso)
import Data.Typeable
import Control.Monad.State (get, put, State, StateT)
import Control.Monad.State.Lazy as S

--------------------------------------------------------
--Traversals
--------------------------------------------------------

(.*$.) :: (Applicative g, Typeable a, Typeable b) => g (FixLang f (a -> b)) -> g (FixLang f a) -> g (FixLang f b)
x .*$. y = (:!$:) <$> x <*> y

genChildren :: forall a b f . (BoundVars f, Typeable a, Typeable b) => Traversal' (FixLang f b) (FixLang f a)
genChildren g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
           case eqT :: Maybe (t' :~: a) of
                    Just Refl -> (\x y -> x :!$: LLam y) <$> genChildren g q <*> modify h
                       where bv = scopeUniqueVar q (LLam h)
                             abstractBv f x = subBoundVar bv x f
                             modify h = abstractBv <$> g (h bv)
                    _ -> (\x y -> x :!$: LLam y) <$> genChildren g q <*> modify h
                       where bv = scopeUniqueVar q (LLam h)
                             abstractBv f x = subBoundVar bv x f
                             modify h = abstractBv <$> genChildren g (h bv)
genChildren g phi@(h :!$: (t :: FixLang f tt)) =
                   case ( eqT :: Maybe ((tt -> b) :~: a)
                        , eqT :: Maybe (tt:~: a)
                        ) of (Nothing, Just Refl)  -> genChildren g h .*$. g t
                             (Just Refl, Nothing)  -> g h .*$. genChildren g t
                             --XXX: missing case is ruled out by occurs check
                             _    -> genChildren g h .*$. genChildren g t
genChildren g phi = pure phi

instance (BoundVars f, Typeable a)  => Plated (FixLang f a) where
        plate = genChildren

class Plated (FixLang f (syn sem)) => RelabelVars f syn sem where

    relabelVars :: [String] -> FixLang f (syn sem) -> FixLang f (syn sem)
    relabelVars vs phi = S.evalState (transformM trans phi) vs
        where trans :: FixLang f (syn sem) -> S.State [String] (FixLang f (syn sem))
              trans x = do l <- S.get
                           case l of
                             (label:labels) ->
                               case subBinder x label of
                                Just relabeled -> do S.put labels
                                                     return relabeled
                                Nothing -> return x
                             _ -> return x

    subBinder :: FixLang f (syn sem) -> String -> Maybe (FixLang f (syn sem))

    --XXX: could be changed to [[String]], with subBinder also returning an
    --index, in order to accomodate simultaneous relabelings of several types of variables

--------------------------------------------------------
--Prisms
--------------------------------------------------------

class ReLex f where
        relex :: f idx a -> f idy a

instance ReLex (Predicate pred) where
        relex (Predicate p a) = Predicate p a

instance ReLex (Connective con) where
        relex (Connective p a) = Connective p a

instance ReLex (Function func) where
        relex (Function p a) = Function p a

instance ReLex (Subnective sub) where
        relex (Subnective p a) = Subnective p a

instance ReLex SubstitutionalVariable where
        relex (SubVar n) = SubVar n
        relex (StaticVar n) = StaticVar n

instance ReLex (Binders bind ) where
        relex (Bind q) = Bind q

instance ReLex (Abstractors abs) where
        relex (Abstract abs) = Abstract abs

instance ReLex (Applicators app) where
        relex (Apply app) = Apply app

instance ReLex EndLang

instance (ReLex f, ReLex g) => ReLex (f :|: g) where
        relex (FLeft l) = FLeft (relex l)
        relex (FRight l) = FRight (relex l)

relexIso :: ReLex f => Iso' (f idx a) (f idy a)
relexIso = iso relex relex

data Flag a f g where
        Flag :: {checkFlag :: a} -> Flag a f g
    deriving (Show)

class PrismLink f g where
        link :: Typeable a => Prism' (f a) (g a) 
        pflag :: Flag Bool f g --const False indicates that we don't have a prism here

instance {-# OVERLAPPABLE #-} PrismLink f f where
        link = prism' id Just
        pflag = Flag True

instance PrismLink ((f :|: g) idx) ((f :|: g) idx) where
        link = prism' id Just
        pflag = Flag True

instance {-# OVERLAPPABLE #-} PrismLink f g where
        link = error "you need to define an instance of PrismLink to do this"
        pflag = Flag False

_FLeft :: Prism' ((f :|: g) idx a) (f idx a)
_FLeft = prism' FLeft un
    where un (FLeft s) = Just s
          un _ = Nothing

_FRight :: Prism' ((f :|: g) idx a) (g idx a)
_FRight = prism' FRight un
    where un (FRight s) = Just s
          un _ = Nothing

instance {-# OVERLAPPABLE #-} (PrismLink (f idx) h, PrismLink (g idx) h) => PrismLink ((f :|: g) idx) h where

        link 
            | checkFlag (pflag :: Flag Bool (f idx) h) = _FLeft  . ll
            | checkFlag (pflag :: Flag Bool (g idx) h) = _FRight . rl
            | otherwise = error "No instance found for PrismLink"
            where ll = link :: Typeable a => Prism' (f idx a) (h a)
                  rl = link :: Typeable a => Prism' (g idx a) (h a)

        pflag = Flag $ checkFlag (pflag :: Flag Bool (f idx) h) || checkFlag (pflag :: Flag Bool (g idx) h)

_Fx :: Typeable a => Prism' (Fix f a) (f (Fix f) a)
_Fx = prism' Fx un
    where un (Fx s) = Just s

instance (PrismLink (f (Fix f)) h) => PrismLink (Fix f) h where

        link = _Fx . link

        pflag = Flag $ checkFlag (pflag :: Flag Bool (f (Fix f)) h)

class f :<: g where
        sublang :: Prism' (FixLang g a) (FixLang f a)
        sublang = prism' liftLang lowerLang
        liftLang :: FixLang f a -> FixLang g a
        liftLang = review sublang
        lowerLang :: FixLang g a -> Maybe (FixLang f a)
        lowerLang = preview sublang

instance {-# OVERLAPPABLE #-} (PrismLink (g (FixLang g)) (f (FixLang g)), ReLex f) => f :<: g where
        liftLang (x :!$: y) = liftLang x :!$: liftLang y 
        liftLang (LLam f) = LLam $ liftLang . f . unMaybe . lowerLang
            where unMaybe (Just a) = a
                  unMaybe Nothing = error "lifted lambda given bad argument"
        liftLang (Fx (FLeft (Lift x))) = Fx . FLeft . Lift $ x
        liftLang (FX a) = FX $ review' (link' . relexIso) a
            where link' :: Typeable a => Prism' (g (FixLang g) a) (f (FixLang g) a)
                  link' = link
                  review' :: Prism' b a -> a -> b
                  review' = review

        lowerLang (x :!$: y) = (:!$:) <$> lowerLang x <*> lowerLang y
        lowerLang (LLam f) = Just $ LLam (unMaybe . lowerLang . f . liftLang)
            where unMaybe (Just a) = a
                  unMaybe Nothing = error "lowered lambda returning bad value"
        lowerLang (Fx (FLeft (Lift x))) = Just . Fx . FLeft . Lift $ x
        lowerLang (FX a) = FX <$> preview (link' . relexIso) a
            where link' :: Typeable a => Prism' (g (FixLang g) a) (f (FixLang g) a)
                  link' = link

class (PrismLink (FixLang lex) (SubstitutionalVariable (FixLang lex))) 
        => PrismSubstitutionalVariable lex where

        _substIdx :: Typeable t => Prism' (FixLang lex t) Int
        _substIdx = link_PrismSubstitutionalVar . substIdx

        _staticIdx :: Typeable t => Prism' (FixLang lex t) Int
        _staticIdx = link_PrismSubstitutionalVar . staticIdx

        link_PrismSubstitutionalVar :: Typeable t => Prism' (FixLang lex t) (SubstitutionalVariable (FixLang lex) t)
        link_PrismSubstitutionalVar = link 

        staticIdx :: Prism' (SubstitutionalVariable (FixLang lex) t) Int
        staticIdx  = prism' StaticVar
                            (\x -> case x of StaticVar n -> Just n
                                             _ -> Nothing)

        substIdx :: Prism' (SubstitutionalVariable (FixLang lex) t) Int
        substIdx  = prism' SubVar
                           (\x -> case x of SubVar n -> Just n
                                            _ -> Nothing)
                                            
instance PrismSubstitutionalVariable lex => StaticVar (FixLang lex) where
        static = review _staticIdx
        
instance (Monad m, PrismSubstitutionalVariable lex) => MonadVar (FixLang lex) (StateT Int m) where
        fresh = do n <- get
                   put (n+1)
                   return $ review _substIdx n

        freshPig = do n <- get 
                      put (n+1)
                      return $ EveryPig $ review _substIdx n

{-| Transforms a prism selecting a nullary constructor for a unary language
item into a prism onto the things that that item is predicated of. e.g.
if you have a NOT in your language, selected by a prism, this would give
you a prism on to the argument to a negation
-}
unaryOpPrism :: (Typeable a, Typeable b) => Prism' (FixLang lex (a -> b)) () -> Prism' (FixLang lex b) (FixLang lex a) 
unaryOpPrism prism = unaryOpPrismOn prism . withUnit

withUnit :: Iso' ((),a) a
withUnit = iso (\((),x) -> x) (\x -> ((),x)) 

flipt :: Iso' (a,b) (b,a)
flipt = iso (\(x,y) -> (y,x)) (\(x,y) -> (y,x))

unaryOpPrismOn :: (Typeable a, Typeable b) => 
    Prism' (FixLang lex (a -> b)) c -> Prism' (FixLang lex b) (c, FixLang lex a) 
unaryOpPrismOn prism = prism' construct (destruct prism) 
    where construct (c,a) = review prism c :!$: a

          destruct :: Typeable a => Prism' (FixLang lex (a -> b)) c -> FixLang lex b -> Maybe (c, FixLang lex a)
          destruct (prism :: Prism' (FixLang lex (a -> b)) c) b@(h :!$: (t:: FixLang lex t)) =
              case eqT :: Maybe (a :~: t) of 
                        Just Refl -> (,) <$> preview prism h <*> Just t
                        Nothing -> Nothing
          destruct _ _ = Nothing

{-| Similarly, for a binary language item -}
binaryOpPrism :: (Typeable a, Typeable c, Typeable b) => 
    Prism' (FixLang lex (a -> b -> c)) () -> Prism' (FixLang lex c) (FixLang lex a, FixLang lex b)
binaryOpPrism prism = binaryOpPrismOn prism . withUnit

binaryOpPrismOn :: (Typeable a, Typeable c, Typeable b) => 
    Prism' (FixLang lex (a -> b -> c)) d -> Prism' (FixLang lex c) (d, (FixLang lex a, FixLang lex b))
binaryOpPrismOn prism = prism' construct (destruct prism)
    where construct (c,(a,b)) = review prism c :!$: a :!$: b

          destruct :: (Typeable b, Typeable a) => Prism' (FixLang lex (a -> b -> c)) d -> FixLang lex c -> Maybe (d,(FixLang lex a, FixLang lex b))
          destruct (prism :: Prism' (FixLang lex (a -> b -> c)) d) b@(h :!$: (t:: FixLang lex a') :!$: (t':: FixLang lex b')) =
              case eqT :: Maybe ((a,b) :~: (a',b')) of 
                        Just Refl -> (,) <$> preview prism h <*> Just (t,t')
                        Nothing -> Nothing
          destruct _ _ = Nothing
