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
    SupportsND r (OpenLexicon lex) sem => 
    NaturalDeductionCalc r (OpenLexicon lex) sem -> a) -> String 
      -> Maybe a
ofSetTheorySys f sys 
        | sys == "elementarySetTheory"       = Just $ f estCalc 
        | sys == "separativeSetTheory"       = Just $ f sstCalc
        | otherwise                          = Nothing

ofSetTheoryTreeSys :: (forall r lex . 
                    ( Show r
                    , SupportsND r (OpenLexicon lex) (Form Bool)
                    , StructuralInference r (OpenLexicon lex) (ProofTree r (OpenLexicon lex) (Form Bool))
                    , StructuralOverride r (ProofTree r (OpenLexicon lex) (Form Bool))
                 ) => 
              TableauCalc (OpenLexicon lex) (Form Bool) r -> a) -> String -> Maybe a
ofSetTheoryTreeSys f sys | sys == "openLogicSTNK"              = Just $ f openLogicSTNKCalc
                         | otherwise                           = Nothing
