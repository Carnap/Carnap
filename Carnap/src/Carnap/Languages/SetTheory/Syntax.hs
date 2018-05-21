{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, AutoDeriveTypeable #-}
module Carnap.Languages.SetTheory.Syntax 
where

import Carnap.Core.Util 
import Control.Monad.State
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConstructors
import Data.List (intercalate)


-------------------------------------
--  1. Data for Set Theory Syntax  --
-------------------------------------

type SetTheoryElem = TermElem Bool Int

type SetTheoryEq = TermEq Bool Int

type SetTheorySubset = TermSubset Bool Int

type SetTheorySchematicPred = SchematicIntPred Bool Int

type OpenLexicon a = CoreLexicon :|: Predicate SetTheoryElem :|: Predicate SetTheoryEq :|: a
--XXX: as an extension of FOL, this falls under all the classes of PureFirstOrderLex a = CoreLexicon :|: a

instance PrismPolyadicSchematicPredicate (OpenLexicon a) Int Bool
instance PrismTermElements (OpenLexicon a) Int Bool
instance PrismTermEquality (OpenLexicon a) Int Bool

-------------------------------------
--  2. Strict First-Order Lexicon  --
-------------------------------------

type StrictSetTheoryLex = OpenLexicon EndLang

type StrictSetTheoryLang = FixLang StrictSetTheoryLex

-----------------------------------------
--  3. Elementary First-Order Lexicon  --
-----------------------------------------

type ElementaryOps = ElementarySetOperations Int

type ElementarySetTheoryLexOpen a = OpenLexicon (Function ElementaryOps :|: Predicate SetTheorySubset :|: a )

type ElementarySetTheoryLex = ElementarySetTheoryLexOpen EndLang

type ElementarySetTheoryLang = FixLang ElementarySetTheoryLex

instance PrismElementarySetsLex (ElementarySetTheoryLexOpen a) Int
instance PrismTermSubset (ElementarySetTheoryLexOpen a) Int Bool
