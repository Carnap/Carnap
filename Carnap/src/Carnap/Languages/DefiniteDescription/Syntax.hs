{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, TypeOperators, PatternSynonyms, FlexibleContexts #-}
module Carnap.Languages.DefiniteDescription.Syntax where

import Carnap.Core.Util 
import Carnap.Core.Data.Util 
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.PureFirstOrder.Logic.Rules (seqVar)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Control.Lens (Traversal', preview, outside, (^?), (%~), (.~), (&), Prism')
import Data.Typeable (Typeable)

-----------------------------------------------
--  1. Data for Definite Description Logics  --
-----------------------------------------------

type FregeanDescription = DefiniteDescription Bool Int --"fregean" because every term has a denotation.

-----------------------------------------
--  2. Definite Description Languages  --
-----------------------------------------

type FregeanDescLex = PureLexiconFOL :|: Binders FregeanDescription :|: EndLang

type FregeanDescLang = FixLang FregeanDescLex

instance PrismDefiniteDesc FregeanDescLex Bool Int
instance PrismPropLex FregeanDescLex Bool
instance PrismSchematicProp FregeanDescLex Bool
instance PrismIndexedConstant FregeanDescLex Int
instance PrismPolyadicPredicate FregeanDescLex Int Bool
instance PrismPolyadicSchematicPredicate FregeanDescLex Int Bool
instance PrismPolyadicFunction FregeanDescLex Int Int
instance PrismPolyadicSchematicFunction FregeanDescLex Int Int
instance PrismTermEquality FregeanDescLex Int Bool
instance PrismBooleanConnLex FregeanDescLex Bool
instance PrismBooleanConst FregeanDescLex Bool
instance PrismGenericTypedLambda FregeanDescLex Term Form Int
instance PrismStandardVar FregeanDescLex Int
instance PrismSubstitutionalVariable FregeanDescLex
instance PrismGenericQuant FregeanDescLex Term Form Bool Int
instance PrismQuantContext FregeanDescLex Bool Int

instance Incrementable FregeanDescLex (Term Int) where
    incHead = const Nothing
        & outside (_predIdx')  .~ (\(n,a) -> Just $ ppn n (ASucc a))
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_funcIdx')  .~ (\(n,a) -> Just $ pfn n (ASucc a))
        & outside (_sfuncIdx') .~ (\(n,a) -> Just $ spfn n (ASucc a))
        where _predIdx' :: Typeable ret => Prism' (FregeanDescLang ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _predIdx' = _predIdx
              _spredIdx' :: Typeable ret => Prism' (FregeanDescLang ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _spredIdx' = _spredIdx
              _funcIdx' :: Typeable ret => Prism' (FregeanDescLang ret) (Int, Arity (Term Int) (Term Int) ret) 
              _funcIdx' = _funcIdx
              _sfuncIdx' :: Typeable ret => Prism' (FregeanDescLang ret) (Int, Arity (Term Int) (Term Int) ret) 
              _sfuncIdx' = _sfuncIdx

instance BoundVars FregeanDescLex where

    scopeUniqueVar q (LLam f) = case castTo $ foVar $ show $ maxVar (LLam f) + 1 of
                                    Just x -> x
                                    Nothing -> error "cast failed in ScopeUniqueVar"

    scopeUniqueVar _ _ = undefined

    subBoundVar = saferSubst

instance Eq (FregeanDescLang sem) where (==) = (=*)

type FregeanDescSeq = ClassicalSequentOver FregeanDescLex

instance CopulaSchema FregeanDescLang where 

    appSchema q@(Fx _) (LLam f) e = case ( qtype q >>= preview _all >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         , dtype q >>= preview _desc >>= \x -> (,) <$> Just x <*> castTo (foVar x)
                                         ) of
                                     (Just (x,v), _,_) -> schematize (All x) (show (f v) : e)
                                     (_, Just (x,v),_) -> schematize (Some x) (show (f v) : e)
                                     (_, _, Just (x,v))-> schematize (DefinDesc x) (show (f v) : e)
                                     _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance CopulaSchema FregeanDescSeq where 

    appSchema q@(Fx _) (LLam f) e = case ( qtype q >>= preview _all >>= \x -> (,) <$> Just x <*> castTo (seqVar x)
                                         , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (seqVar x)
                                         , dtype q >>= preview _desc >>= \x -> (,) <$> Just x <*> castTo (seqVar x)
                                         ) of
                                     (Just (x,v), _,_) -> schematize (All x) (show (f v) : e)
                                     (_, Just (x,v),_) -> schematize (Some x) (show (f v) : e)
                                     (_, _, Just (x,v))-> schematize (DefinDesc x) (show (f v) : e)
                                     _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance  RelabelVars FregeanDescLex Form Bool where

    subBinder (q :!$: LLam f) y =  case ( qtype q >>= preview _all
                                        , qtype q >>= preview _some
                                        , oftype (LLam f)) of
                                    (Just _, _, Just (LLam f')) -> Just $ lall y f'
                                    (_, Just _, Just (LLam f')) -> Just $ lsome y f'
                                    _ -> Nothing
    subBinder _ _ = Nothing

instance  RelabelVars FregeanDescLex Term Int where

    subBinder (q :!$: LLam f) y =  case ( dtype q >>= preview _desc , oftype (LLam f)) of
                                    (Just _, Just (LLam f')) -> Just $ ddesc y f'
                                    _ -> Nothing
    subBinder _ _ = Nothing

instance CanonicalForm (FregeanDescLang (Form Bool)) where

    canonical = relabelVars [i ++ j | i <- ["x"], j <- map show [1 ..]] . (termsOf %~ relabelVars [i ++ j | i <- ["y"], j <- map show [1 ..]])

instance HasLiterals FregeanDescLex Bool where
    isAtom a | (a ^? _propIndex) /= Nothing = True
             | (a ^? binaryOpPrism _termEq') /= Nothing = True
             | otherwise = withHead (\h -> not . null $ h ^? _predIdx') a
        where _predIdx' :: Typeable ret => Prism' (FregeanDescLang ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _predIdx' = _predIdx
              _termEq' :: Prism' (FregeanDescLang (Term Int -> Term Int -> Form Bool)) ()
              _termEq' = _termEq

instance Eq (FregeanDescSeq sem) where (==) = (=*)

dtype :: Typeable a => FixLang lex a -> Maybe (FixLang lex ((Term Int -> Form Bool)-> Term Int))
dtype = castTo
