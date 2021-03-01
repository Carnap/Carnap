{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, TypeOperators, ScopedTypeVariables, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.HigherOrderArithmetic.Syntax 
where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Util
import Carnap.Core.Data.Classes
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.Arithmetic.Syntax

type UntypedHigherOrderArithLex = ExtendedSeparativeSetTheoryLexOpen ( Predicate ArithLessThan :|: Function ArithOps)

type UntypedHigherOrderArithLang = FixLang UntypedHigherOrderArithLex

instance PrismTermLessThan UntypedHigherOrderArithLex Int Bool
instance PrismElementaryArithmeticLex UntypedHigherOrderArithLex Int
