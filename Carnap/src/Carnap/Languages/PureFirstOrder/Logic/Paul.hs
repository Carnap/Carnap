{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Paul where

import Text.Parsec
import Data.List (intercalate)
import Carnap.Core.Data.Types (Form, Term)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Paul
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson hiding (SD,Pr)
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PureFirstOrder.Util

parsePaulPD rtc = try (map PDtoPDE <$> quantRule) 
              <|> try (parseEq) 
              <|> liftProp 
    where liftProp = do r <- parsePaulSD (defaultRuntimeDeductionConfig)
                        return (map (PDtoPDE . SD) r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "P", "A/EE", "Assumption"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r `elem` ["A/EE"] -> return [SD (AS "/∃E")]
                              | r `elem` [ "P","Assumption"] -> return [Pr (problemPremises rtc)]
          parseEq = try (string "=E" >> return [IE1,IE2]) <|> (string "=I" >> return [II])

parsePaulPDProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPDE PureLexiconFOL (Form Bool)]
parsePaulPDProof ders = toDeductionFitchAlt (parsePaulPD ders) paulPDFormulaParser

parsePaulPDE rtc = try liftPD <|> liftPDP
    where liftPDP = map PDPtoPDEP <$> parseLogicBookPDPlus rtc
          liftPD = map PDEtoPDEP <$> parsePaulPD rtc
          --XXX the confusing names here are because what Bergman calls
          --PDE, Paul calls PD, and what Bergman calls PDEPlus, paul calls
          --PDE

parsePaulPDEProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine LogicBookPDEPlus PureLexiconFOL (Form Bool)]
parsePaulPDEProof ders = toDeductionFitchAlt (parsePaulPDE ders) paulPDFormulaParser

paulNotation :: String -> String 
paulNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- try handleQuant <|> try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleQuant = do q <- oneOf "∀∃"
                           v <- anyChar
                           return $ "(" ++ [q] ++ [v] ++ ")"
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- handleTerm `sepBy` char ','
                          char ')'
                          return $ c : concat args
          handleTerm = try handleFunc <|> handleConst
          handleFunc = do c <- oneOf "abcdefghijklmnopqrstuvwxyz" <* char '('
                          args <- handleTerm `sepBy` char ','
                          char ')'
                          return $ [c,'('] ++ intercalate "," args ++ ")"
          handleConst = do c <- oneOf "abcdefghijklmnopqrstuvwxyz" 
                           return [c]
          fallback = do c <- anyChar 
                        return [c]

paulPDCalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parsePaulPDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver paulPDFormulaParser
    , ndParseForm = paulPDFormulaParser
    , ndNotation = paulNotation
    }

paulPDECalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parsePaulPDEProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver paulPDFormulaParser
    , ndParseForm = paulPDFormulaParser
    , ndNotation = paulNotation
    }
