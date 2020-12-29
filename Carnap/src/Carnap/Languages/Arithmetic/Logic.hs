{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.Arithmetic.Logic where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics (ReLex)
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Arithmetic.Syntax
import Carnap.Languages.Arithmetic.Logic.OpenLogic

ofArithmeticTreeSys :: (forall r lex . 
                    ( Show r
                    , SupportsND r (OpenLexiconArith lex) (Form Bool)
                    , StructuralInference r (OpenLexiconArith lex) (ProofTree r (OpenLexiconArith lex) (Form Bool))
                    , StructuralOverride r (ProofTree r (OpenLexiconArith lex) (Form Bool))
                 ) => 
              TableauCalc (OpenLexiconArith lex) (Form Bool) r -> a) -> String -> Maybe a
ofArithmeticTreeSys f sys | sys == "openLogicArithNK"              = Just $ f openLogicArithNKCalc
                          | otherwise                           = Nothing
