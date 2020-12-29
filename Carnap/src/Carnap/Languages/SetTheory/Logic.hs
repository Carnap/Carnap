{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.SetTheory.Logic where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics (ReLex)
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.SetTheory.Logic.OpenLogic
import Carnap.Languages.SetTheory.Logic.Carnap

ofSetTheorySys :: (forall r sem lex . 
    SupportsND r (OpenLexiconST lex) sem => 
    NaturalDeductionCalc r (OpenLexiconST lex) sem -> a) -> String 
      -> Maybe a
ofSetTheorySys f sys 
        | sys == "elementarySetTheory"       = Just $ f estCalc 
        | sys == "separativeSetTheory"       = Just $ f sstCalc
        | otherwise                          = Nothing

ofSetTheoryTreeSys :: (forall r lex . 
                    ( Show r
                    , SupportsND r (OpenLexiconST lex) (Form Bool)
                    , StructuralInference r (OpenLexiconST lex) (ProofTree r (OpenLexiconST lex) (Form Bool))
                    , StructuralOverride r (ProofTree r (OpenLexiconST lex) (Form Bool))
                 ) => 
              TableauCalc (OpenLexiconST lex) (Form Bool) r -> a) -> String -> Maybe a
ofSetTheoryTreeSys f sys | sys == "openLogicSTNK"              = Just $ f openLogicSTNKCalc
                         | otherwise                           = Nothing
