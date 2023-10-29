{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.KooSL
    (parseKooSLProof, kooSLCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.KalishAndMontague (parseMontagueSC, MontagueSC)

--A system for propositional logic resembling the proof system from Kalish
--and Montague's LOGIC, with derived rules, adding Prof. Alex Koo's requested edits.

parseKooSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) 
                     -> String -> [DeductionLine MontagueSC PurePropLexicon (Form Bool)]
parseKooSLProof rtc = toDeductionMontague (parseMontagueSC rtc) (kooSLFormulaParser kooOpts)

kooSLNotation :: String -> String
kooSLNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleChar <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleChar = (char '⊢' >> return "∴")
          fallback = do c <- anyChar 
                        return [c]

kooSLCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseKooSLProof
    , ndProcessLine = processLineMontague
    , ndProcessLineMemo = Nothing
    , ndNotation = kooSLNotation
    } 
