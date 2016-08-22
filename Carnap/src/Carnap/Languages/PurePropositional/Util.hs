module Carnap.Languages.PurePropositional.Util (showClean,isValid, isEquivTo) where

import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PurePropositional.Syntax
import Control.Lens.Plated (universe)
import Control.Lens
import Data.Maybe
import Data.List

--------------------------------------------------------
--1. Show Clean
--------------------------------------------------------

showClean :: PurePropLanguage (Form Bool) -> String
showClean (x@(_ :||: _) :->: y@(_ :||: _))  = dropBoth   PIf x y
showClean (x@(_ :&: _) :->: y@(_ :||: _))   = dropBoth   PIf x y
showClean (x@(_ :||: _) :->: y@(_ :&: _))   = dropBoth   PIf x y
showClean (x@(_ :&: _) :->: y@(_ :&: _))    = dropBoth   PIf x y
showClean (x@(_ :||: _) :<->: y@(_ :||: _)) = dropBoth   PIff x y
showClean (x@(_ :&: _) :<->: y@(_ :||: _))  = dropBoth   PIff x y
showClean (x@(_ :||: _) :<->: y@(_ :&: _))  = dropBoth   PIff x y
showClean (x@(_ :&: _) :<->: y@(_ :&: _))   = dropBoth   PIff x y
showClean (x :->: y@(_ :||: _))             = dropSecond PIf x y
showClean (x :->: y@(_ :&: _))              = dropSecond PIf x y
showClean (x :<->: y@(_ :||: _))            = dropSecond PIff x y
showClean (x :<->: y@(_ :&: _))             = dropSecond PIff x y
showClean (x@(_ :||: _) :->: y)             = dropFirst PIf x y
showClean (x@(_ :&: _) :->: y)              = dropFirst PIf x y
showClean (x@(_ :&: _) :&: y)               = dropFirst PAnd x y
showClean (x@(_ :||: _) :||: y)             = dropFirst POr x y
showClean (PNeg x)                          = noDrop PNot x
showClean x                                 = show x
    
dropParens :: PurePropLanguage (Form Bool) -> String
dropParens =  init . tail . showClean

dropBoth :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> String
dropBoth x y z = schematize x [dropParens y, dropParens z]

dropFirst :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> String
dropFirst x y z = schematize x [dropParens y, showClean z]

dropSecond :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> String
dropSecond x y z = schematize x [showClean y, dropParens z]

noDrop :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> String 
noDrop x y = schematize x [showClean y]

dropOutermost :: String -> String
dropOutermost s@('(':xs) = init . tail $ s
dropOutermost s = s

--------------------------------------------------------
--2. Truth Tables
--------------------------------------------------------

getIndicies :: PurePropLanguage (Form Bool) -> [Int]
getIndicies = catMaybes . map (preview propIndex) . universe

getValuations = (map toValuation) . subsequences. getIndicies 
    where toValuation l = \x -> x `elem` l

isValid p = and $ map (\v -> unform $ satisfies v p) (getValuations p)
    where unform (Form x) = x

isEquivTo x y = isValid (x :<->: y)
