{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.SetTheory.Syntax 
where

import Control.Lens
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util
import Carnap.Core.Data.Classes
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.GenericConstructors

-------------------------------------
--  1. Data for Set Theory Syntax  --
-------------------------------------

type SetTheoryElem = TermElem Bool Int

type SetTheoryEq = TermEq Bool Int

type SetTheorySubset = TermSubset Bool Int

type SetTheorySchematicPred = SchematicIntPred Bool Int

type OpenLexiconST a = CoreLexicon :|: Predicate SetTheoryElem :|: Predicate SetTheoryEq :|: Predicate PureSchematicPred :|:  Function PureSchematicFunction :|: a
--XXX: as an extension of FOL, this falls under all the classes of PureFirstOrderLexWith a = CoreLexicon :|: a

instance PrismPolyadicSchematicPredicate (OpenLexiconST a) Int Bool
instance PrismPolyadicSchematicFunction (OpenLexiconST a) Int Int
instance PrismTermElements (OpenLexiconST a) Int Bool
instance PrismTermEquality (OpenLexiconST a) Int Bool

-------------------------------------
--  2. Strict First-Order Lexicon  --
-------------------------------------

type StrictSetTheoryLex = OpenLexiconST EndLang

type StrictSetTheoryLang = FixLang StrictSetTheoryLex

-----------------------------------------
--  3. Elementary First-Order Lexicon  --
-----------------------------------------

type ElementaryOps = ElementarySetOperations Int

type ElementarySetTheoryLexOpen a = OpenLexiconST (Function ElementaryOps :|: Predicate SetTheorySubset :|: a )

type ElementarySetTheoryLex = ElementarySetTheoryLexOpen EndLang

type ElementarySetTheoryLang = FixLang ElementarySetTheoryLex

instance PrismElementarySetsLex (ElementarySetTheoryLexOpen a) Int
instance PrismTermSubset (ElementarySetTheoryLexOpen a) Int Bool

-----------------------------------------
--  3. Separative First-Order Lexicon  --
-----------------------------------------

type SetTheorySep = Separation Int Bool

type SeparativeSetTheoryLexOpen a = ElementarySetTheoryLexOpen SetTheorySep

type SeparativeSetTheoryLex = SeparativeSetTheoryLexOpen EndLang

type SeparativeSetTheoryLang = FixLang SeparativeSetTheoryLex

instance CopulaSchema SeparativeSetTheoryLang where 

    appSchema t@(x :!$: y) (LLam f) e = case ( castTo x :: Maybe (SeparativeSetTheoryLang (Term Int -> (Term Int -> Form Bool) -> Term Int))
                                             , castTo (LLam f) :: Maybe (SeparativeSetTheoryLang (Term Int -> Form Bool))) of
                                            (Just x, Just (LLam f)) -> case x ^? _separator :: Maybe String of
                                              Just s -> schematize t (show (f $ foVar s) : e)
                                              Nothing -> schematize t (show (LLam f) : e)
                                            _ -> schematize t (show (LLam f) : e)
    appSchema h@(Fx _) (LLam f) e = case (qtype h >>= preview _all, qtype h >>= preview _some, oftype (LLam f)) of
                                    (Just x, _, Just (LLam f')) -> schematize (All x) (show (f' $ foVar x) : e)
                                    (_, Just x, Just (LLam f')) -> schematize (Some x) (show (f' $ foVar x) : e)
                                    _ -> schematize h (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

instance PrismSeparating SeparativeSetTheoryLex Int Bool
