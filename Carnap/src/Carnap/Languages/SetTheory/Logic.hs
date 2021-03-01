{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.SetTheory.Logic where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Util
import Carnap.Core.Data.Optics (ReLex)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.SetTheory.Logic.OpenLogic
import Carnap.Languages.SetTheory.Logic.Carnap

ofSetTheorySys :: (forall r lex . 
    ( SupportsND r (OpenLexiconST lex) (Form Bool)
    , Incrementable (OpenLexiconST lex) (Term Int)
    ) => NaturalDeductionCalc r (OpenLexiconST lex) (Form Bool)-> a) -> String 
      -> Maybe a
ofSetTheorySys f sys 
        | sys == "elementarySetTheory"       = Just $ f estCalc 
        | sys == "separativeSetTheory"       = Just $ f sstCalc
        | otherwise                          = Nothing

ofSetTheoryTreeSys :: (forall r lex . 
                    ( Show r
                    , SupportsND r (OpenLexiconST lex) (Form Bool)
                    , Incrementable (OpenLexiconST lex) (Term Int)
                    , StructuralInference r (OpenLexiconST lex) (ProofTree r (OpenLexiconST lex) (Form Bool))
                    , StructuralOverride r (ProofTree r (OpenLexiconST lex) (Form Bool))
                 ) => 
              TableauCalc (OpenLexiconST lex) (Form Bool) r -> a) -> String -> Maybe a
ofSetTheoryTreeSys f sys | sys == "openLogicSTNK"              = Just $ f openLogicSTNKCalc
                         | sys == "openLogicExSTNK"            = Just $ f openLogicExSTNKCalc
                         | sys == "openLogicESTNK"             = Just $ f openLogicESTNKCalc
                         | sys == "openLogicExESTNK"           = Just $ f openLogicExESTNKCalc
                         | sys == "openLogicSSTNK"             = Just $ f openLogicSSTNKCalc
                         | sys == "openLogicExSSTNK"           = Just $ f openLogicExSSTNKCalc
                         | otherwise                           = Nothing
