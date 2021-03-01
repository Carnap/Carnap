{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.HigherOrderArithmetic.Logic where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics (ReLex)
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.HigherOrderArithmetic.Syntax
import Carnap.Languages.HigherOrderArithmetic.Logic.OpenLogic
import Carnap.Languages.Util.LanguageClasses

ofHigherOrderArithmeticTreeSys :: (forall r . 
                    ( Show r
                    , SupportsND r UntypedHigherOrderArithLex (Form Bool)
                    , StructuralInference r UntypedHigherOrderArithLex (ProofTree r UntypedHigherOrderArithLex (Form Bool))
                    , StructuralOverride r (ProofTree r UntypedHigherOrderArithLex (Form Bool))
                ) => TableauCalc UntypedHigherOrderArithLex (Form Bool) r -> a) -> String -> Maybe a
ofHigherOrderArithmeticTreeSys f sys | sys == "openLogicExHOArithNK"    = Just $ f openLogicArithExHOArithNKCalc
                                     | otherwise                        = Nothing
