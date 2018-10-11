{-#LANGUAGE  UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, GADTs, PolyKinds, TypeOperators, RankNTypes, FlexibleContexts, ScopedTypeVariables  #-}
module Carnap.Core.Data.Optics(
  LangTypes2(..), LangTypes1(..), RelabelVars(..),  PrismLink(..),
  (:<:)(..), ReLex(..), unaryOpPrism, binaryOpPrism, GenericChildren(..),
) where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Control.Lens(Plated(..), Prism'(..), prism', preview, Iso'(..), iso, review, Traversal'(..),transformM)
import Data.Typeable
import qualified Control.Monad.State.Lazy as S

--------------------------------------------------------
--Traversals
--------------------------------------------------------

(.*$.) :: (Applicative g, Typeable a, Typeable b) => g (FixLang f (a -> b)) -> g (FixLang f a) -> g (FixLang f b)
x .*$. y = (:!$:) <$> x <*> y

handleArg1 :: (Applicative g, LangTypes1 f syn1 sem1)
          => Maybe (tt :~: syn1 sem1) -> (FixLang f (syn1 sem1)
            -> g (FixLang f (syn1 sem1))) -> FixLang f tt -> g (FixLang f tt)
handleArg1 (Just Refl) f l = f l
handleArg1 Nothing     _ l = pure l

handleArg2 :: (Applicative g, LangTypes2 f syn1 sem1 syn2 sem2)
          => (Maybe (tt :~: syn1 sem1), Maybe (tt :~: syn2 sem2))
          -> (FixLang f (syn1 sem1) -> g (FixLang f (syn1 sem1)))
          -> FixLang f tt
          -> g (FixLang f tt)
handleArg2 (Just Refl, _) f l = f l
handleArg2 (_, Just Refl) f l = difChildren2 f l
handleArg2 (_, _)         _ l = pure l

class (Typeable syn1, Typeable sem1, Typeable syn2, Typeable sem2, BoundVars f) => LangTypes2 f syn1 sem1 syn2 sem2 | f syn1 sem1 -> syn2 sem2 where

        simChildren2 :: Traversal' (FixLang f (syn1 sem1)) (FixLang f (syn1 sem1))
        simChildren2 g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case ( eqT :: Maybe (t' :~: syn1 sem1)
                        , eqT :: Maybe (t' :~: syn2 sem2)) of
                            (Just Refl, _) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h bv)
                            (_ , Just Refl) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (difChildren2 g $ h bv)
                            _ -> pure phi
        simChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22, r31, r32) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2) .*$. (handleArg2 (r31, r32) g t3)
        simChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2)
        simChildren2 g phi@(h :!$: (t1 :: FixLang f tt))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                ) of (r11, r12) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1)
        simChildren2 g phi = pure phi

        difChildren2 :: Traversal' (FixLang f (syn2 sem2)) (FixLang f (syn1 sem1))
        difChildren2 g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case ( eqT :: Maybe (t' :~: syn1 sem1)
                        , eqT :: Maybe (t' :~: syn2 sem2)) of
                            (Just Refl, _) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)
                            (_ , Just Refl) -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (difChildren2 g $ h $ bv)
                            _ -> pure phi
        difChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22, r31, r32) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2) .*$. (handleArg2 (r31, r32) g t3)
        difChildren2 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn2 sem2)
                                ) of (r11, r12, r21, r22) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1) .*$. (handleArg2 (r21, r22) g t2)
        difChildren2 g phi@(h :!$: (t1 :: FixLang f tt))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt :~: syn2 sem2)
                                ) of (r11, r12) ->
                                         pure h .*$. (handleArg2 (r11, r12) g t1)
        difChildren2 g phi = pure phi

class (Typeable syn1, Typeable sem1, BoundVars f) => LangTypes1 f syn1 sem1 where

        simChildren1 ::  Traversal' (FixLang f (syn1 sem1)) (FixLang f (syn1 sem1))
        simChildren1 g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case eqT :: Maybe (t' :~: syn1 sem1) of
                            Just Refl -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)
                            Just Refl -> (\x y -> x :!$: LLam y) <$> pure q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)

        simChildren1 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2)
                             :!$: (t3 :: FixLang f tt3))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                , eqT :: Maybe (tt3 :~: syn1 sem1)
                                ) of (r1,  r2,  r3) ->
                                         pure h .*$. (handleArg1 r1 g t1) .*$. (handleArg1 r2 g t2) .*$. (handleArg1 r3 g t3)
        simChildren1 g phi@(h :!$: (t1 :: FixLang f tt)
                             :!$: (t2 :: FixLang f tt2))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                , eqT :: Maybe (tt2 :~: syn1 sem1)
                                ) of (r1, r2) ->
                                         pure h .*$. (handleArg1 r1 g t1) .*$. (handleArg1 r2 g t2)
        simChildren1 g phi@(h :!$: (t1 :: FixLang f tt))=
                           case ( eqT :: Maybe (tt :~: syn1 sem1)
                                ) of r1 -> pure h .*$. (handleArg1 r1 g t1)
        simChildren1 g phi = pure phi

class (Typeable a, BoundVars f) => GenericChildren f a where

        genChildren :: Typeable b => Traversal' (FixLang f b) (FixLang f a)
        genChildren g phi@(q :!$: LLam (h :: FixLang f t -> FixLang f t')) =
                   case eqT :: Maybe (t' :~: a) of
                            Just Refl -> (\x y -> x :!$: LLam y) <$> genChildren g q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (g $ h $ bv)
                            _ -> (\x y -> x :!$: LLam y) <$> genChildren g q <*> modify h
                               where bv = scopeUniqueVar q (LLam h)
                                     abstractBv f = \x -> (subBoundVar bv x f)
                                     modify h = abstractBv <$> (genChildren g $ h $ bv)
        genChildren g phi@(h :!$: (t1 :: FixLang f tt))=
                           case ( eqT :: Maybe (tt :~: a)
                                ) of (Just Refl) -> genChildren g h .*$. g t1
                                     _ -> genChildren g h .*$. genChildren g t1
        genChildren g phi = pure phi


instance {-# OVERLAPPABLE #-} 
        ( BoundVars f
        , Typeable syn1
        , Typeable sem1
        , LangTypes2 f syn1 sem1 syn2 sem2) => LangTypes1 f syn1 sem1 where

        simChildren1 = simChildren2

instance LangTypes1 f syn sem  => Plated (FixLang f (syn sem)) where
        plate = simChildren1

class (Plated (FixLang f (syn sem)), BoundVars f) => RelabelVars f syn sem where

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

instance {-# OVERLAPPABLE #-} PrismLink f f where
        link = prism' id Just
        pflag = Flag True

instance PrismLink ((f :|: g) idx) ((f :|: g) idx) where
        link = prism' id Just
        pflag = Flag True

class PrismLink f g where
        link :: Typeable a => Prism' (f a) (g a) 
        pflag :: Flag Bool f g --const False indicates that we don't have a prism here

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

        pflag = Flag $ checkFlag ((pflag :: Flag Bool (f idx) h)) || checkFlag ((pflag :: Flag Bool (g idx) h))

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
        liftLang (FX a) = FX $ review' (link' . relexIso) a
            where link' :: Typeable a => Prism' (g (FixLang g) a) (f (FixLang g) a)
                  link' = link
                  review' :: Prism' b a -> a -> b
                  review' = review

        lowerLang (x :!$: y) = (:!$:) <$> lowerLang x <*> lowerLang y
        lowerLang (LLam f) = Just $ LLam (unMaybe . lowerLang . f . liftLang)
            where unMaybe (Just a) = a
                  unMaybe Nothing = error "lowered lambda returning bad value"
        lowerLang (FX a) = FX <$> preview (link' . relexIso) a
            where link' :: Typeable a => Prism' (g (FixLang g) a) (f (FixLang g) a)
                  link' = link

{-| Transforms a prism selecting a nullary constructor for a unary language
item into a prism onto the things that that item is predicated of. e.g.
if you have a NOT in your language, selected by a prism, this would give
you a prism on to the argument to a negation
-}
unaryOpPrism :: (Typeable a, Typeable b) => 
    Prism' (FixLang lex (a -> b)) () -> Prism' (FixLang lex b) (FixLang lex a) 
unaryOpPrism prism = prism' construct (destruct prism) 
    where construct a = review prism () :!$: a

          destruct :: Typeable a => Prism' (FixLang lex (a -> b)) () -> FixLang lex b -> Maybe (FixLang lex a)
          destruct (prism :: Prism' (FixLang lex (a -> b)) ()) b@(h :!$: (t:: FixLang lex t)) =
              case eqT :: Maybe (a :~: t) of 
                        Just Refl -> preview prism h >> return t
                        Nothing -> Nothing
          destruct _ _ = Nothing

{-| Similarly, for a binary language item -}
binaryOpPrism :: (Typeable a, Typeable c, Typeable b) => 
    Prism' (FixLang lex (a -> b -> c)) () -> Prism' (FixLang lex c) (FixLang lex a, FixLang lex b)
binaryOpPrism prism = prism' construct (destruct prism)
    where construct (a,b) = review prism () :!$: a :!$: b

          destruct :: (Typeable b, Typeable a) => Prism' (FixLang lex (a -> b -> c)) () -> FixLang lex c -> Maybe (FixLang lex a, FixLang lex b)
          destruct (prism :: Prism' (FixLang lex (a -> b -> c)) ()) b@(h :!$: (t:: FixLang lex a') :!$: (t':: FixLang lex b')) =
              case eqT :: Maybe ((a,b) :~: (a',b')) of 
                        Just Refl -> preview prism h >> return (t,t')
                        Nothing -> Nothing
          destruct _ _ = Nothing

