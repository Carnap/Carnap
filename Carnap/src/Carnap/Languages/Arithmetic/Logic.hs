{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.Arithmetic.Logic where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics (ReLex)
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Arithmetic.Syntax
import Carnap.Languages.Arithmetic.Logic.OpenLogic
import Carnap.Languages.Util.LanguageClasses

ofArithmeticTreeSys :: (forall r lex . 
                    ( Show r
                    , SupportsND r (OpenLexiconArith lex) (Form Bool)
                    , Incrementable (OpenLexiconArith lex) (Term Int)
                    , StructuralInference r (OpenLexiconArith lex) (ProofTree r (OpenLexiconArith lex) (Form Bool))
                    , StructuralOverride r (ProofTree r (OpenLexiconArith lex) (Form Bool))
                 ) => 
              TableauCalc (OpenLexiconArith lex) (Form Bool) r -> a) -> String -> Maybe a
ofArithmeticTreeSys f sys | sys == "openLogicArithNK"              = Just $ f openLogicArithNKCalc
                          | sys == "openLogicExArithNK"            = Just $ f openLogicExtendedArithNKCalc
                          | otherwise                              = Nothing
