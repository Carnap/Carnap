{-#LANGUAGE GADTs, UndecidableInstances, ScopedTypeVariables, ConstraintKinds, FlexibleContexts, RankNTypes, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Logic.Rules where

import Control.Lens
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.Util
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Types
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.SetTheory.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors

------------------------
--  1.1 Simple Rules  --
------------------------

type ElementarySetTheoryConstraint lex b = 
        ( FirstOrderConstraints lex b
        , SubsetLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , ElemLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , EqLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , ElementarySetsLanguage (ClassicalSequentOver lex (Term Int))
        ) 

type ElementarySetTheoryRule lex b = ElementarySetTheoryConstraint lex b => SequentRule lex (Form b)

type ElementarySetTheoryRuleVariants lex b = ElementarySetTheoryConstraint lex b => [SequentRule lex (Form b)]

--XXX Needed because of variable binding in separators
instance ( ReLex a
         , Schematizable (a (ClassicalSequentOver (SeparativeSetTheoryLexOpen a)))
         ) => CopulaSchema (ClassicalSequentOver (SeparativeSetTheoryLexOpen a)) where 

    appSchema q@(Fx _) (LLam f) e = 
        case ( q 
             , qtype q >>= preview _all >>= \x -> (,) <$> Just x <*> castTo (seqVar x)
             , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (seqVar x)
             ) of (x :!$: y, _, _) -> case ( castTo x :: Maybe (ClassicalSequentOver (SeparativeSetTheoryLexOpen a) (Term Int -> (Term Int -> Form Bool) -> Term Int))
                         , castTo (LLam f) :: Maybe (ClassicalSequentOver (SeparativeSetTheoryLexOpen a) (Term Int -> Form Bool))) of
                        (Just x, Just (LLam f)) -> case x ^? _separator :: Maybe String of
                          Just s -> schematize q (show (f $ seqVar s) : e)
                          Nothing -> schematize q (show (LLam f) : e)
                        _ -> schematize q (show (LLam f) : e)
                  (_, Just (x,v), _) -> schematize (All x) (show (f v) : e)
                  (_, _, Just (x,v)) -> schematize (Some x) (show (f v) : e)
                  _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

unpackUnion :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackUnion = replace ((tau `isIn` tau') .\/. (tau `isIn` tau'')) (tau `isIn` (tau' `setUnion` tau''))

unpackIntersection :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackIntersection = replace ((tau `isIn` tau') ./\. (tau `isIn` tau'')) (tau `isIn` (tau' `setIntersect` tau''))

unpackPowerset :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackPowerset = replace (tau `within` tau') (tau `isIn` (powerset tau'))

unpackComplement :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackComplement = replace ((tau `isIn` tau')./\. lneg (tau `isIn` tau''))  (tau `isIn` (tau' `setComplement` tau')) ++
                   replace (lneg (tau `isIn` tau'') ./\. lneg (tau `isIn` tau'))  (tau `isIn` (tau' `setComplement` tau'))

unpackEquality :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackEquality = replace (tau `equals` tau') (lall "v" $ \x -> (x `isIn` tau) .<=>. (x `isIn` tau')) ++
                 replace (tau `equals` tau') (lall "v" $ \x -> (x `isIn` tau') .<=>. (x `isIn` tau))

unpackEmptySet :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackEmptySet = replace (tau `equals` emptySet) (lall "v" $ \x -> lneg (x `isIn` tau)) ++
                 replace (emptySet `equals` tau') (lall "v" $ \x -> lneg (x `isIn` tau))

unpackSubset :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackSubset = replace (tau `within` tau') (lall "v" $ \x -> (x `isIn` tau) .=>. (x `isIn` tau'))

----------------------------
--  1.2 Separation rules  --
----------------------------

type SeparationSetTheoryConstraint lex b = 
        ( FirstOrderConstraints lex b
        , ElemLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , SeparatingLang (ClassicalSequentOver lex (Form b)) (ClassicalSequentOver lex (Term Int)) 
        )

type SeparatingSetTheoryVariants lex b = SeparationSetTheoryConstraint lex b => [SequentRule lex (Form b)]

unpackSeparation :: forall b lex. IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => SeparatingSetTheoryVariants lex b
unpackSeparation = replace ((seperator tau) ./\. (tau `isIn` tau')) (tau `isIn` separate "v" tau' seperator) ++
                   replace ((tau `isIn` tau') ./\. (seperator tau)) (tau `isIn` separate "v" tau' seperator)
   where seperator = phi 1 :: ClassicalSequentOver lex (Term Int) -> ClassicalSequentOver lex (Form b)
