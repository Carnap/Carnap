{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.PureSecondOrder.Logic (psolCalc, msolCalc, ofSecondOrderSys) where

import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.PureSecondOrder.Logic.Carnap
import Carnap.Languages.PureSecondOrder.Logic.Gamut

--TODO: Cleanup SOL data types so we can get a more specific type here.
ofSecondOrderSys :: (forall r sem lex . 
    SupportsND r (OpenSOLLex lex) sem => 
    NaturalDeductionCalc r (OpenSOLLex lex) sem -> a) -> String 
      -> Maybe a
ofSecondOrderSys f sys | sys == "secondOrder"             = Just $ f msolCalc 
                       | sys == "polyadicSecondOrder"     = Just $ f psolCalc
                       | sys == "gamutNDSOL"              = Just $ f gamutNDSOLCalc
                       | otherwise                        = Nothing
