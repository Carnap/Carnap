{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Carnap.Languages.PureFirstOrder.Util (propForm, boundVarOf, toPNF, universalDepth, existentialDepth, comparableMatricies, removeBlock, pnfEquiv, toAllPNF, nonDeterministicStepPNF) where

import Carnap.Core.Data.Classes
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Control.Monad.State
import Control.Lens
import Data.Typeable (Typeable)
import Data.Maybe
import Data.List

propForm f = evalState (propositionalize f) []
    where propositionalize = nonBoolean
            & outside (binaryOpPrism _and) .~ (\(x,y) -> land <$> propositionalize x <*> propositionalize y)
            & outside (binaryOpPrism _or) .~ (\(x,y) -> lor <$> propositionalize x <*> propositionalize y)
            & outside (binaryOpPrism _if) .~ (\(x,y) -> lif <$> propositionalize x <*> propositionalize y)
            & outside (binaryOpPrism _iff) .~ (\(x,y) -> liff <$> propositionalize x <*> propositionalize y)
            & outside (unaryOpPrism _not) .~ (\x -> lneg <$> propositionalize x)
          
          nonBoolean form = do abbrev <- get
                               case elemIndex form abbrev of
                                   Just n -> return (pn n)
                                   Nothing -> put (abbrev ++ [form]) >> return (pn $ length abbrev)
                                    
boundVarOf v f = case preview  _varLabel v >>= subBinder f of
                            Just f' -> show f' == show f
                            Nothing -> False 

toPNF = canonical . rewrite stepPNF

toAllPNF = map canonical . rewriteM nonDeterministicStepPNF

stepPNF :: FixLang PureLexiconFOL (Form Bool) -> Maybe (FixLang PureLexiconFOL (Form Bool))
stepPNF = const Nothing 
            & outside (binaryOpPrism _and . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f ./\. f' x ))
            & outside (binaryOpPrism _and . otherside (unaryOpPrismOn _all')) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f' x ./\. f ))
            & outside (binaryOpPrism _and . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f ./\. f' x ))
            & outside (binaryOpPrism _and . flipt . aside (unaryOpPrismOn _some') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f' x ./\. f ))
            & outside (binaryOpPrism _or . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f .\/. f' x ))
            & outside (binaryOpPrism _or . otherside (unaryOpPrismOn _all')) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f' x .\/. f ))
            & outside (binaryOpPrism _or . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f .\/. f' x ))
            & outside (binaryOpPrism _or . otherside (unaryOpPrismOn _some')) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f' x .\/. f ))
            & outside (binaryOpPrism _if . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f .=>. f' x ))
            & outside (binaryOpPrism _if . otherside (unaryOpPrismOn _all')) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _if . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f .=>. f' x ))
            & outside (binaryOpPrism _if . otherside (unaryOpPrismOn _some')) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f .=>. f' x ) ./\. (lsome v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . otherside (unaryOpPrismOn _all')) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f .=>. f' x ) ./\. (lsome v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f .=>. f' x ) ./\. (lall v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . otherside (unaryOpPrismOn _some')) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f .=>. f' x ) ./\. (lall v $ \x -> f' x .=>. f ))
            & outside (unaryOpPrism _not . unaryOpPrismOn _some') .~
                (\(v, LLam f') -> Just $ (lall v $ \x -> lneg $ f' x ))
            & outside (unaryOpPrism _not . unaryOpPrismOn _all') .~
                (\(v, LLam f') -> Just $ (lsome v $ \x -> lneg $ f' x ))
    where _all' :: Prism' (FixLang PureLexiconFOL ((Term Int -> Form Bool) -> Form Bool)) String
          _all' = _all
          _some' :: Prism' (FixLang PureLexiconFOL ((Term Int -> Form Bool) -> Form Bool)) String
          _some' = _some
          otherside p = flipt . aside p . flipt

nonDeterministicStepPNF :: FixLang PureLexiconFOL (Form Bool) -> [Maybe (FixLang PureLexiconFOL (Form Bool))]
nonDeterministicStepPNF = pure . stepPNF
    & outside (binaryOpPrism _and . aside (unaryOpPrismOn _all') . otherside (unaryOpPrismOn _some')) .~
                (\((ve, LLam g),(va, LLam f)) -> 
                    [ Just $ (lall va $ \x -> lsome ve $ \y -> ( g y ./\. f x))
                    , Just $ (lsome ve $ \x -> lall va $ \y -> ( g x ./\. f y))
                    ])
    & outside (binaryOpPrism _and . aside (unaryOpPrismOn _some') . otherside (unaryOpPrismOn _all')) .~
                (\((va, LLam g),(ve, LLam f)) -> 
                    [ Just $ (lall va $ \x -> lsome ve $ \y -> ( g x ./\. f y))
                    , Just $ (lsome ve $ \x -> lall va $ \y -> ( g y ./\. f x))
                    ])
    & outside (binaryOpPrism _or . aside (unaryOpPrismOn _all') . otherside (unaryOpPrismOn _some')) .~
                (\((ve, LLam g),(va, LLam f)) -> 
                    [ Just $ (lall va $ \x -> lsome ve $ \y -> ( g y .\/. f x))
                    , Just $ (lsome ve $ \x -> lall va $ \y -> ( g x .\/. f y))
                    ])
    & outside (binaryOpPrism _or . aside (unaryOpPrismOn _some') . otherside (unaryOpPrismOn _all')) .~
                (\((va, LLam g),(ve, LLam f)) -> 
                    [ Just $ (lall va $ \x -> lsome ve $ \y -> ( g x .\/. f y))
                    , Just $ (lsome ve $ \x -> lall va $ \y -> ( g y .\/. f x))
                    ])
    & outside (binaryOpPrism _if . aside (unaryOpPrismOn _all') . otherside (unaryOpPrismOn _all')) .~
                (\((ve, LLam g),(va, LLam f)) -> 
                    [ Just $ (lall va $ \x -> lsome ve $ \y -> ( g y .=>. f x))
                    , Just $ (lsome ve $ \x -> lall va $ \y -> ( g x .=>. f y))
                    ])
    & outside (binaryOpPrism _if . aside (unaryOpPrismOn _some') . otherside (unaryOpPrismOn _some')) .~
                (\((va, LLam g),(ve, LLam f)) -> 
                    [ Just $ (lall va $ \x -> lsome ve $ \y -> ( g x .=>. f y))
                    , Just $ (lsome ve $ \x -> lall va $ \y -> ( g y .=>. f x))
                    ])
    where _all' :: Prism' (FixLang PureLexiconFOL ((Term Int -> Form Bool) -> Form Bool)) String
          _all' = _all
          _some' :: Prism' (FixLang PureLexiconFOL ((Term Int -> Form Bool) -> Form Bool)) String
          _some' = _some
          otherside p = flipt . aside p . flipt

universalDepth = const 0 & outside (unaryOpPrismOn _all') .~ (\(v, LLam f) -> 1 + universalDepth (f $ foVar v))
    where _all' :: Prism' (FixLang (OpenLexiconPFOL b) ((Term Int -> Form Bool) -> Form Bool)) String
          _all' = _all

instantiate f t = inst f
        where inst = const f & outside (unaryOpPrismOn _all) .~ (\(v, LLam g) -> g t)
                             & outside (unaryOpPrismOn _some) .~ (\(v, LLam g) -> g t)

existentialDepth = const 0 & outside (unaryOpPrismOn _some') .~ (\(v, LLam f) -> 1 + existentialDepth (f $ foVar v))
    where _some' :: Prism' (FixLang (OpenLexiconPFOL b) ((Term Int -> Form Bool) -> Form Bool)) String
          _some' = _some

comparableMatricies f g = recur f g (map show [1 ..])
    where recur f g vars | qdepth f > 0 = do (f',g') <- removeBlock f g vars
                                             recur f' g' (drop (qdepth f) vars)
          recur f g v = [(f,g)]
          qdepth f = max (universalDepth f) (existentialDepth f)

pnfEquiv f g = any (== True) theCases
    where theCases = do (f',g') <- comparableMatricies (toPNF f) (toPNF g)
                        return $ isValid (propForm (f' .<=>. g'))


removeBlock f g vars | udf > 0 && udf == udg = revar f g (take udf vars) (take udf vars)
                     | edf > 0 && edf == edg = revar f g (take edf vars) (take edf vars)
                     | otherwise = []
    where udf = universalDepth f
          udg = universalDepth g
          edf = existentialDepth f
          edg = existentialDepth g
          revar f g [] _ = [(f,g)]
          revar f g fvars gvars = do fv <- fvars
                                     gv <- gvars
                                     revar (instantiate f (foVar fv)) (instantiate g (foVar gv)) (fvars \\ [fv]) (gvars \\ [gv])

--- XXX: This shouldn't require so many annotations. Doesn't need them in
--GHCi 8.4.2, and probably not in GHC 8.4.2 generally.
instance ( FirstOrderLex (b (FixLang (OpenLexiconPFOL b)))
         , ToSchema (OpenLexiconPFOL b) (Term Int)
         ) => ToSchema (OpenLexiconPFOL b) (Form Bool) where
    toSchema = transform ((maphead trans & outside _propIndex .~ (\n -> phin n)) . (terms %~ toSchema))
        where trans :: ( PrismLink (b (FixLang (OpenLexiconPFOL b))) (Predicate (SchematicIntPred Bool Int) (FixLang (OpenLexiconPFOL b))) 
                       , PrismLink (b (FixLang (OpenLexiconPFOL b))) (Predicate (IntPred Bool Int) (FixLang (OpenLexiconPFOL b)))
                       , PrismLink (b (FixLang (OpenLexiconPFOL b))) (SubstitutionalVariable (FixLang (OpenLexiconPFOL b)))
                       , Typeable a) => OpenLanguagePFOL b a -> OpenLanguagePFOL b a
              trans = id & outside (_predIdx') .~ (\(n,a) -> pphin n a)
              _predIdx' :: ( PrismLink (b (FixLang (OpenLexiconPFOL b))) (Predicate (IntPred Bool Int) (FixLang (OpenLexiconPFOL b)))
                           , Typeable ret) => Prism' (OpenLanguagePFOL b ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _predIdx' = _predIdx
              terms :: ( PrismLink (b (FixLang (OpenLexiconPFOL b))) (SubstitutionalVariable (FixLang (OpenLexiconPFOL b)))
                       , FirstOrderLex (b (FixLang (OpenLexiconPFOL b)))
                       ) => Traversal' (FixLang (OpenLexiconPFOL b) (Form Bool)) (FixLang (OpenLexiconPFOL b) (Term Int))
              terms = genChildren

instance {-# OVERLAPPABLE #-} FirstOrderLex (b (FixLang (OpenLexiconPFOL b))) => ToSchema (OpenLexiconPFOL b) (Term Int) where
    toSchema = id

instance {-# OVERLAPS #-} ToSchema PureLexiconFOL (Term Int) where
    toSchema = transform (maphead trans & outside _constIdx .~ (\n -> taun n))
        where trans :: Typeable a => FixLang PureLexiconFOL a -> FixLang PureLexiconFOL a
              trans = id & outside (_funcIdx') .~ (\(n,a) -> spfn n a)
              _funcIdx' :: Typeable ret => Prism' (FixLang PureLexiconFOL ret) (Int, Arity (Term Int) (Term Int) ret) 
              _funcIdx' = _funcIdx
