module Carnap.Languages.PureFirstOrder.Logic.Belot
    ( belotPDECalc, belotPDCalc, belotPDPlusCalc, belotPDEPlusCalc) where

import Text.Parsec
import Data.Char
import Data.List (intercalate)
import Carnap.Core.Data.Types (Form)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Languages.ClassicalSequent.Parser

parseBelotPDProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPD PureLexiconFOL (Form Bool)]
parseBelotPDProof rtc = toDeductionFitchAlt (parseLogicBookPD rtc) belotPDFormulaParser

parseBelotPDPlusProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPDPlus PureLexiconFOL (Form Bool)]
parseBelotPDPlusProof rtc = toDeductionFitchAlt (parseLogicBookPDPlus rtc) belotPDFormulaParser

parseBelotPDEProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPDE PureLexiconFOL (Form Bool)]
parseBelotPDEProof rtc = toDeductionFitchAlt (parseLogicBookPDE rtc) belotPDEFormulaParser

parseBelotPDEPlusProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPDEPlus PureLexiconFOL (Form Bool)]
parseBelotPDEPlusProof rtc = toDeductionFitchAlt (parseLogicBookPDEPlus rtc) belotPDEFormulaParser

belotNotation :: String -> String 
belotNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleCon <|> try handleQuant <|> try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleCon = (char '∧' >> return "&") 
                      <|> (char '¬' >> return "~") 
                      <|> (char '→' >> return "⊃")
                      <|> (char '↔' >> return "≡")
                      <|> (char '⊤' >> return "")
          handleQuant = do q <- oneOf "∀∃"
                           v <- anyChar
                           return $ "(" ++ [q] ++ [v] ++ ")"
          handleAtom = try handlePred <|> handleSent
          handlePred = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- handleTerm `sepBy` char ','
                          char ')'
                          return $ c : concat args
          handleSent = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                          return $ [toLower c]
          handleTerm = try handleFunc <|> handleConst
          handleFunc = do c <- oneOf "abcdefghijklmnopqrstuvwxyz" <* char '('
                          args <- handleTerm `sepBy` char ','
                          char ')'
                          return $ [c,'('] ++ intercalate "," args ++ ")"
          handleConst = do c <- oneOf "abcdefghijklmnopqrstuvwxyz" 
                           return [c]
          fallback = do c <- anyChar 
                        return [c]

belotPDCalc = logicBookPDCalc 
    { ndParseProof = parseBelotPDProof
    , ndParseSeq = parseSeqOver belotPDFormulaParser
    , ndParseForm = belotPDFormulaParser
    , ndNotation = belotNotation
    }

belotPDPlusCalc = logicBookPDPlusCalc 
    { ndParseProof = parseBelotPDPlusProof 
    , ndParseSeq = parseSeqOver belotPDFormulaParser
    , ndParseForm = belotPDFormulaParser
    , ndNotation = belotNotation
    }

belotPDECalc = logicBookPDECalc 
    { ndParseProof = parseBelotPDEProof
    , ndParseSeq = parseSeqOver belotPDEFormulaParser
    , ndParseForm = belotPDEFormulaParser
    , ndNotation = belotNotation
    }

belotPDEPlusCalc = logicBookPDEPlusCalc 
    { ndParseProof = parseBelotPDEPlusProof 
    , ndParseSeq = parseSeqOver belotPDEFormulaParser
    , ndParseForm = belotPDEFormulaParser
    , ndNotation = belotNotation
    }
