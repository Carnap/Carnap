{-# LANGUAGE TypeOperators #-}
module Carnap.Good where

import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PurePropositional.Syntax

test = pflag :: Flag Bool ((Connective PureConn :|: Predicate PureProp) PurePropLanguage) (Connective PureConn PurePropLanguage)
