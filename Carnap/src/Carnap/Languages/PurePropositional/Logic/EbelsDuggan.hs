{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.EbelsDuggan 
    (parseEbelsDugganTFL, EbelsDugganTFL,  ebelsDugganTFLCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.ThomasBolducAndZach

data EbelsDugganTFL = TBZ ThomasBolducAndZachTFL
                    | RAA1 | RAA2 | RAA3 | RAA4 
                    | EFQ | DIL | HS | DNI | AndComm1 | AndComm2 | OrComm1
                    | OrComm2 | IffComm1 | IffComm2 | MC1 | MC2 | MC3 | MC4 
                    | BCE1 | BCE2 | NC1 | NC2 | BCT1 | BCT2 | TC | FA
                    deriving (Eq)

instance Show EbelsDugganTFL where
         show (TBZ x) = show x
         show RAA1 = "RAA"
         show RAA2 = "RAA"
         show RAA3 = "RAA"
         show RAA4 = "RAA"
         show EFQ = "EFQ"
         show DIL = "DIL"
         show HS = "HS"
         show DNI = "DNI"
         show AndComm1 = "Comm"
         show AndComm2 = "Comm"
         show OrComm1 = "Comm"
         show OrComm2 = "Comm"
         show IffComm1 = "Comm"
         show IffComm2 = "Comm"
         show MC1 = "MC"
         show MC2 = "MC"
         show MC3 = "MC"
         show MC4 = "MC"
         show BCE1 = "↔ex"
         show BCE2 = "↔ex"
         show NC1 = "NC"
         show NC2 = "NC"
         show BCT1 = "BCT"
         show BCT2 = "BCT"
         show TC = "TC"
         show FA = "FA"

instance Inference EbelsDugganTFL PurePropLexicon (Form Bool) where
        ruleOf (TBZ x) = ruleOf x
        ruleOf RAA1 = constructiveReductioVariations !! 0 
        ruleOf RAA2 = constructiveReductioVariations !! 1
        ruleOf RAA3 = constructiveReductioVariations !! 2
        ruleOf RAA4 = constructiveReductioVariations !! 3
        ruleOf EFQ = exfalso
        ruleOf DIL = dilemma
        ruleOf HS = hypotheticalSyllogism
        ruleOf DNI = doubleNegationIntroduction
        ruleOf AndComm1 = andCommutativity !! 0
        ruleOf AndComm2 = andCommutativity !! 1
        ruleOf OrComm1 = orCommutativity !! 0
        ruleOf OrComm2 = orCommutativity !! 1
        ruleOf IffComm1 = iffCommutativity !! 0
        ruleOf IffComm2 = iffCommutativity !! 1
        ruleOf MC1 = materialConditional !! 0
        ruleOf MC2 = materialConditional !! 1
        ruleOf MC3 = materialConditional !! 2
        ruleOf MC4 = materialConditional !! 3
        ruleOf BCE1 = biconditionalExchange !! 0
        ruleOf BCE2 = biconditionalExchange !! 1
        ruleOf NC1 = negatedConditional !! 0
        ruleOf NC2 = negatedConditional !! 1
        ruleOf BCT1 = biconditionalPonensVariations !! 0
        ruleOf BCT2 = biconditionalPonensVariations !! 1
        ruleOf TC = materialConditionalVariations !! 0
        ruleOf FA = materialConditionalVariations !! 1

        indirectInference (TBZ x) = indirectInference x
        indirectInference x
             | x `elem` [RAA1, RAA2, RAA3, RAA4] = Just doubleProof
             | otherwise = Nothing

        isAssumption (TBZ x) = isAssumption x
        isAssumption _  = False

        isPremise (TBZ x) = isPremise x
        isPremise _  = False

        restriction (TBZ x) = restriction x
        restriction _ = Nothing

parseEbelsDugganTFL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [EbelsDugganTFL]
parseEbelsDugganTFL rtc = try ebelsDugganAddition <|>  (map TBZ <$> parseThomasBolducAndZachTFL rtc)
    where ebelsDugganAddition = do r <- choice (map (try . string) ["RAA", "EFQ", "DIL", "HS", "DNI", "Comm", "MC", "↔ex", "<>E", "<->E", "BCE", "NC", "BCT", "TC", "FA"])
                                   return $ case r of
                                          "RAA" -> [RAA1, RAA2, RAA3, RAA4]
                                          "EFQ" -> [EFQ] 
                                          "DIL" -> [DIL]
                                          "HS"  -> [HS]
                                          "DNI" -> [DNI]
                                          "Comm" -> [AndComm1, AndComm2, OrComm1, OrComm2, IffComm1, IffComm2]
                                          "MC" -> [MC1, MC2, MC3, MC4]
                                          "NC" -> [NC1, NC2]
                                          "BCT" -> [BCT1, BCT2]
                                          "TC" -> [TC]
                                          "FA" -> [FA]
                                          r | r `elem` ["↔ex", "<>E", "<->E", "BCE"] -> [BCE1, BCE2]

parseEbelsDugganTFLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine EbelsDugganTFL PurePropLexicon (Form Bool)]
parseEbelsDugganTFLProof rtc = toDeductionFitch (parseEbelsDugganTFL rtc) (purePropFormulaParser thomasBolducZachOpts)

ebelsDugganTFLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseEbelsDugganTFLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZachOpts)
    , ndParseForm = purePropFormulaParser thomasBolducZachOpts
    , ndNotation = thomasBolducAndZachNotation
    }
