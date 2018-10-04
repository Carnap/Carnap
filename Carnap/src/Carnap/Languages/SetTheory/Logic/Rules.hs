{-#LANGUAGE GADTs, ConstraintKinds, FlexibleContexts, RankNTypes, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.SetTheory.Logic.Rules where

import Data.Typeable
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
--Rules without variants

type ElementarySetTheoryConstraint lex b = 
        ( FirstOrderConstraints lex b
        , SubsetLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , ElemLanguage (ClassicalSequentOver lex) (Term Int) (Form b)
        , ElementarySetsLanguage (ClassicalSequentOver lex (Term Int))
        ) 

type ElementarySetTheoryRule lex b = ElementarySetTheoryConstraint lex b => SequentRule lex (Form b)

type ElementarySetTheoryRuleVariants lex b = ElementarySetTheoryConstraint lex b => [SequentRule lex (Form b)]

unpackUnion :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackUnion = replace ((tau `isIn` tau') .\/. (tau `isIn` tau'')) (tau `isIn` (tau' `setUnion` tau''))

unpackIntersection :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackIntersection = replace ((tau `isIn` tau') ./\. (tau `isIn` tau'')) (tau `isIn` (tau' `setIntersect` tau''))

unpackPowerset :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackPowerset = replace (tau `within` tau') (tau `isIn` (powerset tau'))

unpackComplement :: IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b)) => ElementarySetTheoryRuleVariants lex b
unpackComplement = replace ((tau `isIn` tau')./\. lneg (tau `isIn` tau''))  (tau `isIn` (tau' `setComplement` tau')) ++
                   replace (lneg (tau `isIn` tau'') ./\. lneg (tau `isIn` tau'))  (tau `isIn` (tau' `setComplement` tau'))
