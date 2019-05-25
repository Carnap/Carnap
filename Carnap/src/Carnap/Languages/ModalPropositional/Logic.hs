{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.ModalPropositional.Logic
        ( parseHardegreeK, hardegreeKCalc
        , parseHardegreeL, hardegreeLCalc
        , parseHardegreeWTL, hardegreeWTLCalc
        , parseHardegreeB, hardegreeBCalc
        , parseHardegreeT, hardegreeTCalc
        , parseHardegreeD, hardegreeDCalc
        , parseHardegreeFour, hardegreeFourCalc
        , parseHardegreeFive, hardegreeFiveCalc
        , ofModalPropSys
        )
    where

import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.ModalPropositional.Logic.Hardegree


ofModalPropSys :: (forall r sem lex . 
    SupportsND r (ModalPropLexiconWith lex) sem => 
    NaturalDeductionCalc r (ModalPropLexiconWith lex) sem -> a) -> String 
      -> Maybe a
ofModalPropSys f sys | sys == "hardegreeL"                = Just $ f hardegreeLCalc
                     | sys == "hardegreeK"                = Just $ f hardegreeKCalc
                     | sys == "hardegreeD"                = Just $ f hardegreeDCalc
                     | sys == "hardegreeT"                = Just $ f hardegreeTCalc
                     | sys == "hardegreeB"                = Just $ f hardegreeBCalc
                     | sys == "hardegree4"                = Just $ f hardegreeFourCalc
                     | sys == "hardegree5"                = Just $ f hardegreeFiveCalc
                     | sys == "hardegreeWTL"              = Just $ f hardegreeWTLCalc
                     | otherwise                          = Nothing
