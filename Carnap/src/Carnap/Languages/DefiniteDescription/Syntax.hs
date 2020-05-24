{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, TypeOperators, PatternSynonyms, FlexibleContexts #-}
module Carnap.Languages.DefiniteDescription.Syntax where

import Carnap.Core.Util 
import Carnap.Core.Data.Util 
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Logic.Rules (seqVar)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Control.Lens (Traversal', preview, outside, (.~), (&), Prism')
import Data.Typeable (Typeable)

-----------------------------------------------
--  1. Data for Definite Description Logics  --
-----------------------------------------------

type FregeanDescription = DefiniteDescription Bool Int --"fregean" because every term has a denotation.

-----------------------------------------
--  2. Definite Description Languages  --
-----------------------------------------

type FregeanDescLex = OpenLexiconFOL (Binders FregeanDescription :|: EndLang)

instance PrismDefiniteDesc FregeanDescLex Bool Int

type FregeanDescLang = FixLang FregeanDescLex

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

instance Eq (FregeanDescSeq sem) where (==) = (=*)

dtype :: Typeable a => FixLang lex a -> Maybe (FixLang lex ((Term Int -> Form Bool)-> Term Int))
dtype = castTo
