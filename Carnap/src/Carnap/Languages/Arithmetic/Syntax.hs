{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.Arithmetic.Syntax 
where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors

-- TODO: Eventually, consider more fine-grained language distinctions here.

-------------------------------------
--  1. Data for Arithmetic Syntax  --
-------------------------------------

type ArithLessThan = TermLessThan Bool Int

type ArithEq = TermEq Bool Int

type ArithSchematicPred = SchematicIntPred Bool Int

type ArithOps = ElementaryArithmeticOperations Int

type OpenLexiconArith a = CoreLexicon :|: Predicate ArithLessThan :|: Predicate ArithEq 
                       :|: Predicate ArithSchematicPred :|: Function ArithOps :|: Function PureSchematicFunction :|: a
--XXX: as an extension of FOL, this falls under all the classes of PureFirstOrderLexWith a = CoreLexicon :|: a

instance PrismPolyadicSchematicPredicate (OpenLexiconArith a) Int Bool
instance PrismPolyadicSchematicFunction (OpenLexiconArith a) Int Int
instance PrismTermLessThan (OpenLexiconArith a) Int Bool
instance PrismTermEquality (OpenLexiconArith a) Int Bool
instance PrismElementaryArithmeticLex (OpenLexiconArith a) Int

-------------------------------------
--  2. Strict First-Order Lexicon  --
-------------------------------------

type ArithLex = OpenLexiconArith EndLang

type ArithLang = FixLang ArithLex
