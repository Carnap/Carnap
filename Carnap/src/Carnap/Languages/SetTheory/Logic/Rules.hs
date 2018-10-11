{-#LANGUAGE GADTs, ScopedTypeVariables, ConstraintKinds, FlexibleContexts, RankNTypes, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Logic.Rules where

import Data.Typeable
import Carnap.Core.Data.Util (scopeHeight)
import Data.List (intercalate)
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.SetTheory.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
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

instance CopulaSchema (ClassicalSequentOver ElementarySetTheoryLex) where 

    appSchema (SeqQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SeqV x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SeqV x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

instance Eq (ClassicalSequentOver ElementarySetTheoryLex a) where (==) = (=*)

instance ParsableLex (Form Bool) ElementarySetTheoryLex where
        langParser = elementarySetTheoryParser

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

----------------------------
--  1.2 Separation rules  --
----------------------------

type SeparationSetTheoryConstraint lex b = 
        ( FirstOrderConstraints lex b
        , ElemLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , SeparatingLang (ClassicalSequentOver lex (Form b)) (ClassicalSequentOver lex (Term Int)) 
        )

type SeparatingSetTheoryVariants lex b = SeparationSetTheoryConstraint lex b => [SequentRule lex (Form b)]

unpackSepration :: forall b. forall lex. IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => SeparatingSetTheoryVariants lex b
unpackSepration = replace ((seperator tau) ./\. (tau `isIn` tau')) (tau `isIn` separate "v" tau' seperator)
    where seperator = phi 1 :: ClassicalSequentOver lex (Term Int) -> ClassicalSequentOver lex (Form b)
