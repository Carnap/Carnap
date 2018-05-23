module Carnap.Calculi.NaturalDeduction.Parser 
    ( toProofTreeStructuredFitch, toProofTreeHardegree, toProofTreeMontague
    , toProofTreeFitch, toDeductionMontague, toDeductionFitch, toDeductionHardegree ) where

import Carnap.Calculi.NaturalDeduction.Parser.Montague
import Carnap.Calculi.NaturalDeduction.Parser.Hardegree
import Carnap.Calculi.NaturalDeduction.Parser.Fitch
import Carnap.Calculi.NaturalDeduction.Parser.StructuredFitch
