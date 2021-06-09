module Carnap.Languages.PurePropositional.Logic.Belot
    ( belotSDCalc, belotSDPlusCalc ) where

import Text.Parsec
import Data.Char
import Carnap.Core.Data.Types (Form)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
import Carnap.Languages.ClassicalSequent.Parser

parseBelotSDProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine LogicBookSD PurePropLexicon (Form Bool)]
parseBelotSDProof ders = toDeductionFitchAlt (parseLogicBookSD ders) (purePropFormulaParser belotOpts)

parseBelotSDPlusProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine LogicBookSDPlus PurePropLexicon (Form Bool)]
parseBelotSDPlusProof ders = toDeductionFitchAlt (parseLogicBookSDPlus ders) (purePropFormulaParser belotOpts)

belotNotation :: String -> String 
belotNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleCon <|> try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleCon = (char '∧' >> return "&") 
                      <|> (char '¬' >> return "~") 
                      <|> (char '→' >> return "⊃")
                      <|> (char '↔' >> return "≡")
                      <|> (char '⊤' >> return "")
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                          return $ [toLower c]
          fallback = do c <- anyChar 
                        return [c]

belotSDCalc = logicBookSDCalc 
    { ndParseProof = parseBelotSDProof
    , ndParseSeq = parseSeqOver (purePropFormulaParser belotOpts)
    , ndParseForm = purePropFormulaParser belotOpts
    , ndNotation = belotNotation
    }

belotSDPlusCalc = logicBookSDPlusCalc 
    { ndParseProof = parseBelotSDPlusProof 
    , ndParseSeq = parseSeqOver (purePropFormulaParser belotOpts)
    , ndParseForm = purePropFormulaParser belotOpts
    , ndNotation = belotNotation
    }
