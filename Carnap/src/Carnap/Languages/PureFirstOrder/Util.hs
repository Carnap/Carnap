{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Carnap.Languages.PureFirstOrder.Util (propForm, boundVarOf, toPNF) where

import Carnap.Core.Data.Classes
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util
import Carnap.Languages.PurePropositional.Syntax
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

stepPNF :: FixLang PureLexiconFOL (Form Bool) -> Maybe (FixLang PureLexiconFOL (Form Bool))
stepPNF = const Nothing 
            & outside (binaryOpPrism _and . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f ./\. f' x ))
            & outside (binaryOpPrism _and . flipt . aside (unaryOpPrismOn _all') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f' x ./\. f ))
            & outside (binaryOpPrism _and . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f ./\. f' x ))
            & outside (binaryOpPrism _and . flipt . aside (unaryOpPrismOn _some') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f' x ./\. f ))
            & outside (binaryOpPrism _or . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f .\/. f' x ))
            & outside (binaryOpPrism _or . flipt . aside (unaryOpPrismOn _all') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f' x .\/. f ))
            & outside (binaryOpPrism _or . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f .\/. f' x ))
            & outside (binaryOpPrism _or . flipt . aside (unaryOpPrismOn _some') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f' x .\/. f ))
            & outside (binaryOpPrism _if . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f .=>. f' x ))
            & outside (binaryOpPrism _if . flipt . aside (unaryOpPrismOn _all') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _if . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f .=>. f' x ))
            & outside (binaryOpPrism _if . flipt . aside (unaryOpPrismOn _some') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . aside (unaryOpPrismOn _all')) .~
                (\(f,(v, LLam f')) -> Just $ (lall v $ \x -> f .=>. f' x ) ./\. (lsome v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . flipt . aside (unaryOpPrismOn _all') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lall v $ \x -> f .=>. f' x ) ./\. (lsome v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . aside (unaryOpPrismOn _some')) .~
                (\(f,(v, LLam f')) -> Just $ (lsome v $ \x -> f .=>. f' x ) ./\. (lall v $ \x -> f' x .=>. f ))
            & outside (binaryOpPrism _iff . flipt . aside (unaryOpPrismOn _some') . flipt) .~
                (\((v, LLam f'),f) -> Just $ (lsome v $ \x -> f .=>. f' x ) ./\. (lall v $ \x -> f' x .=>. f ))
            & outside (unaryOpPrism _not . unaryOpPrismOn _some') .~
                (\(v, LLam f') -> Just $ (lall v $ \x -> lneg $ f' x ))
            & outside (unaryOpPrism _not . unaryOpPrismOn _all') .~
                (\(v, LLam f') -> Just $ (lsome v $ \x -> lneg $ f' x ))
    where _all' :: Prism' (FixLang PureLexiconFOL ((Term Int -> Form Bool) -> Form Bool)) String
          _all' = _all
          _some' :: Prism' (FixLang PureLexiconFOL ((Term Int -> Form Bool) -> Form Bool)) String
          _some' = _some

--- XXX: This shouldn't require so many annotations. Doesn't need them in
--GHCi 8.4.2, and probably not in GHC 8.4.2 generally.
instance (FirstOrderLex (b (FixLang (OpenLexiconPFOL b))), ToSchema (OpenLexiconPFOL b) (Term Int)) => ToSchema (OpenLexiconPFOL b) (Form Bool) where
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
