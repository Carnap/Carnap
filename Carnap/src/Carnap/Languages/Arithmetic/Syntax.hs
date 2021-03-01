{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.Arithmetic.Syntax 
where

import Control.Lens
import Data.Typeable
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

type ArithOps = ElementaryArithmeticOperations Int

type OpenLexiconArith a = CoreLexicon :|: Predicate ArithLessThan :|: Predicate ArithEq :|: Function ArithOps
                                      :|: Function PureFunction :|: Predicate PureSchematicPred :|: Function PureSchematicFunction 
                                      :|: a
--XXX: as an extension of FOL, this falls under all the classes of PureFirstOrderLexWith a = CoreLexicon :|: a
--The function symbols are not necessarily exposed by the parser, but are necessary for things like skolemization

type OpenLanguageArith a = FixLang (OpenLexiconArith a)

instance PrismPolyadicSchematicPredicate (OpenLexiconArith a) Int Bool
instance PrismPolyadicSchematicFunction (OpenLexiconArith a) Int Int
instance PrismPolyadicFunction (OpenLexiconArith a) Int Int
instance PrismTermLessThan (OpenLexiconArith a) Int Bool
instance PrismTermEquality (OpenLexiconArith a) Int Bool
instance PrismElementaryArithmeticLex (OpenLexiconArith a) Int

instance {-#OVERLAPPABLE#-} Incrementable (OpenLexiconArith a) (Term Int) where
    incHead = const Nothing
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_funcIdx')  .~ (\(n,a) -> Just $ pfn n (ASucc a))
        & outside (_sfuncIdx') .~ (\(n,a) -> Just $ spfn n (ASucc a))
        where _spredIdx' :: Typeable ret => Prism' (OpenLanguageArith a ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _spredIdx' = _spredIdx
              _funcIdx' :: Typeable ret => Prism' (OpenLanguageArith a ret) (Int, Arity (Term Int) (Term Int) ret) 
              _funcIdx' = _funcIdx
              _sfuncIdx' :: Typeable ret => Prism' (OpenLanguageArith a ret) (Int, Arity (Term Int) (Term Int) ret) 
              _sfuncIdx' = _sfuncIdx

-------------------------------------
--  2. Strict First-Order Lexicon  --
-------------------------------------

type ArithLex = OpenLexiconArith EndLang

type ArithLang = FixLang ArithLex

--------------------------------------------------------------
--  2. Extended First-Order Lexicon with String Predicates  --
--------------------------------------------------------------

type ArithStringPred = StringPred Bool Int

type ArithStringFunc = StringFunc Int Int

type ExtendedArithLex = OpenLexiconArith (Predicate ArithStringPred :|: Function ArithStringFunc)

type ExtendedArithLang = FixLang ExtendedArithLex

instance PrismPolyadicStringPredicate ExtendedArithLex Int Bool
instance PrismPolyadicStringFunction ExtendedArithLex Int Int

instance Incrementable ExtendedArithLex (Term Int) where
    incHead = const Nothing
        & outside (_stringPred')  .~ (\(s,a) -> Just $ stringPred s (ASucc a))
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_stringFunc') .~ (\(s,a) -> Just $ stringFunc s (ASucc a))
        & outside (_sfuncIdx') .~ (\(n,a) -> Just $ spfn n (ASucc a))
        & outside (_funcIdx')  .~ (\(n,a) -> Just $ pfn n (ASucc a))
        where _stringPred' :: Typeable ret => Prism' (FixLang ExtendedArithLex ret) (String, Arity (Term Int) (Form Bool) ret) 
              _stringPred' = _stringPred
              _spredIdx' :: Typeable ret => Prism' (FixLang ExtendedArithLex ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _spredIdx' = _spredIdx
              _funcIdx' :: Typeable ret => Prism' (OpenLanguageArith a ret) (Int, Arity (Term Int) (Term Int) ret) 
              _funcIdx' = _funcIdx
              _sfuncIdx' :: Typeable ret => Prism' (FixLang ExtendedArithLex ret) (Int, Arity (Term Int) (Term Int) ret) 
              _sfuncIdx' = _sfuncIdx
              _stringFunc' :: Typeable ret => Prism' (FixLang ExtendedArithLex ret) (String, Arity (Term Int) (Term Int) ret) 
              _stringFunc' = _stringFunc
