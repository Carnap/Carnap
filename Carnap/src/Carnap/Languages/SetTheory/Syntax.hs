{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, TypeOperators, ScopedTypeVariables, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.SetTheory.Syntax 
where

import Data.Typeable
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

type SetTheoryStringPred = StringPred Bool Int

type SetTheoryStringFunc = StringFunc Int Int

type OpenLexiconST a = CoreLexicon :|: Predicate SetTheoryElem :|: Predicate SetTheoryEq 
                                   :|: Predicate PureSchematicPred :|: Function PureSchematicFunction :|: Function PureFunction 
                                   :|: a
--XXX: as an extension of FOL, this falls under all the classes of PureFirstOrderLexWith a = CoreLexicon :|: a
--The function symbols are not necessarily exposed by the parser, but are necessary for things like skolemization

type OpenLanguageST a = FixLang (OpenLexiconST a)

instance PrismPolyadicSchematicPredicate (OpenLexiconST a) Int Bool
instance PrismPolyadicSchematicFunction (OpenLexiconST a) Int Int
instance PrismPolyadicFunction (OpenLexiconST a) Int Int
instance PrismTermElements (OpenLexiconST a) Int Bool
instance PrismTermEquality (OpenLexiconST a) Int Bool
        
instance {-#OVERLAPPABLE#-} Incrementable (OpenLexiconST a) (Term Int) where
    incHead = const Nothing
        & outside (_spredIdx') .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_funcIdx')  .~ (\(n,a) -> Just $ pfn n (ASucc a))
        & outside (_sfuncIdx') .~ (\(n,a) -> Just $ spfn n (ASucc a))
        where _spredIdx' :: Typeable ret => Prism' (OpenLanguageST a ret) (Int, Arity (Term Int) (Form Bool) ret) 
              _spredIdx' = _spredIdx
              _funcIdx' :: Typeable ret => Prism' (OpenLanguageST a ret) (Int, Arity (Term Int) (Term Int) ret) 
              _funcIdx' = _funcIdx
              _sfuncIdx' :: Typeable ret => Prism' (OpenLanguageST a ret) (Int, Arity (Term Int) (Term Int) ret) 
              _sfuncIdx' = _sfuncIdx

-------------------------------------
--  2. Strict First-Order Lexicon  --
-------------------------------------

type StrictSetTheoryLex = OpenLexiconST EndLang

type StrictSetTheoryLang = FixLang StrictSetTheoryLex

-----------------------------------------------
--  2.1 Extended Strict First-Order Lexicon  --
-----------------------------------------------

type ExtendedStrictSetTheoryLex = OpenLexiconST (Predicate SetTheoryStringPred :|: Function SetTheoryStringFunc)

type ExtendedStrictSetTheoryLang = FixLang ExtendedStrictSetTheoryLex

instance PrismPolyadicStringPredicate ExtendedStrictSetTheoryLex Int Bool
instance PrismPolyadicStringFunction ExtendedStrictSetTheoryLex Int Int

-----------------------------------------
--  3. Elementary First-Order Lexicon  --
-----------------------------------------

type ElementaryOps = ElementarySetOperations Int

type ElementarySetTheoryLexOpen a = OpenLexiconST (Function ElementaryOps :|: Predicate SetTheorySubset :|: a )

type ElementarySetTheoryLex = ElementarySetTheoryLexOpen EndLang

type ElementarySetTheoryLang = FixLang ElementarySetTheoryLex

instance PrismElementarySetsLex (ElementarySetTheoryLexOpen a) Int
instance PrismTermSubset (ElementarySetTheoryLexOpen a) Int Bool

---------------------------------------------------
--  3.1 Extended Elementary First-Order Lexicon  --
---------------------------------------------------

type ExtendedElementarySetTheoryLex = ElementarySetTheoryLexOpen (Predicate SetTheoryStringPred :|: Function SetTheoryStringFunc)

type ExtendedElementarySetTheoryLang = FixLang ExtendedElementarySetTheoryLex

instance PrismPolyadicStringPredicate ExtendedElementarySetTheoryLex Int Bool
instance PrismPolyadicStringFunction ExtendedElementarySetTheoryLex Int Int

-----------------------------------------
--  4. Separative First-Order Lexicon  --
-----------------------------------------

type SetTheorySep = Separation Int Bool

type SeparativeSetTheoryLexOpen a = ElementarySetTheoryLexOpen (SetTheorySep :|: a)

type SeparativeSetTheoryLex = SeparativeSetTheoryLexOpen EndLang

type SeparativeSetTheoryLangOpen a = FixLang (SeparativeSetTheoryLexOpen a)

type SeparativeSetTheoryLang = FixLang SeparativeSetTheoryLex

instance Schematizable (a (SeparativeSetTheoryLangOpen a))
        => CopulaSchema (SeparativeSetTheoryLangOpen a) where 

    appSchema t@(x :!$: y) (LLam f) e = case ( castTo x :: Maybe (SeparativeSetTheoryLangOpen a (Term Int -> (Term Int -> Form Bool) -> Term Int))
                                             , castTo (LLam f) :: Maybe (SeparativeSetTheoryLangOpen a (Term Int -> Form Bool))) of
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

instance PrismSeparating (SeparativeSetTheoryLexOpen a) Int Bool

---------------------------------------------------
--  4.1 Extended Separative First-Order Lexicon  --
---------------------------------------------------

type ExtendedSeparativeSetTheoryLex = SeparativeSetTheoryLexOpen (Predicate SetTheoryStringPred :|: Function SetTheoryStringFunc)

type ExtendedSeparativeSetTheoryLang = FixLang ExtendedSeparativeSetTheoryLex

instance PrismPolyadicStringPredicate ExtendedSeparativeSetTheoryLex Int Bool
instance PrismPolyadicStringFunction ExtendedSeparativeSetTheoryLex Int Int
