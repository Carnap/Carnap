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
showClean = dropOutermost . preShowClean

preShowClean :: PurePropLanguage (Form Bool) -> String
preShowClean (x@(_ :||: _) :->: y@(_ :||: _))  = dropBoth   PIf x y
preShowClean (x@(_ :&: _) :->: y@(_ :||: _))   = dropBoth   PIf x y
preShowClean (x@(_ :||: _) :->: y@(_ :&: _))   = dropBoth   PIf x y
preShowClean (x@(_ :&: _) :->: y@(_ :&: _))    = dropBoth   PIf x y
preShowClean (x@(_ :||: _) :<->: y@(_ :||: _)) = dropBoth   PIff x y
preShowClean (x@(_ :&: _) :<->: y@(_ :||: _))  = dropBoth   PIff x y
preShowClean (x@(_ :||: _) :<->: y@(_ :&: _))  = dropBoth   PIff x y
preShowClean (x@(_ :&: _) :<->: y@(_ :&: _))   = dropBoth   PIff x y
preShowClean (x :->: y@(_ :||: _))             = dropSecond PIf x y
preShowClean (x :->: y@(_ :&: _))              = dropSecond PIf x y
preShowClean (x :<->: y@(_ :||: _))            = dropSecond PIff x y
preShowClean (x :<->: y@(_ :&: _))             = dropSecond PIff x y
preShowClean (x@(_ :||: _) :->: y)             = dropFirst PIf x y
preShowClean (x@(_ :&: _) :->: y)              = dropFirst PIf x y
preShowClean (x@(_ :&: _) :&: y)               = dropFirst PAnd x y
preShowClean (x@(_ :||: _) :||: y)             = dropFirst POr x y
preShowClean (PNeg x)                          = noDrop PNot x
preShowClean x                                 = show x
    
dropParens :: PurePropLanguage (Form Bool) -> String
dropParens =  init . tail . preShowClean

dropBoth :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> String
dropBoth x y z = schematize x [dropParens y, dropParens z]

dropFirst :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> String
dropFirst x y z = schematize x [dropParens y, preShowClean z]

dropSecond :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> PurePropLanguage (Form Bool) -> String
dropSecond x y z = schematize x [preShowClean y, dropParens z]

noDrop :: PurePropLanguage a -> PurePropLanguage (Form Bool) -> String 
noDrop x y = schematize x [preShowClean y]

dropOutermost :: String -> String
dropOutermost s@('(':_) = init . tail $ s
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
