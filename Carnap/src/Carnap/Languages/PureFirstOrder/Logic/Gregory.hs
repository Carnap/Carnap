{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gregory where

import Text.Parsec
import Data.List (intercalate)
import Carnap.Core.Data.Types (Form, Term)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Gregory
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson hiding (SD,Pr)
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PureFirstOrder.Util

newtype GregoryPD = GregoryPD { getGregoryPD :: LogicBookPDE }

newtype GregoryPDE = GregoryPDE { getGregoryPDE :: LogicBookPDEPlus }

instance Show GregoryPD where
    show (GregoryPD (PDtoPDE (SD x))) = show (GregorySD x)
    show (GregoryPD (PDtoPDE (Pr _))) = "P"
    show (GregoryPD x) = show x

instance Show GregoryPDE where
    show (GregoryPDE (PDPtoPDEP (SDPlus x))) = show (GregorySDE x)
    show (GregoryPDE (PDPtoPDEP (PDtoPDP x))) = show (GregoryPD (PDtoPDE x))
    show (GregoryPDE x) = show x

instance Inference GregoryPD PureLexiconFOL (Form Bool) where
    ruleOf (GregoryPD x) = ruleOf x

    indirectInference (GregoryPD x) = indirectInference x 

    isAssumption (GregoryPD x) = isAssumption x

    isPremise (GregoryPD x) = isPremise x

    restriction (GregoryPD x) = restriction x

instance Inference GregoryPDE PureLexiconFOL (Form Bool) where
    ruleOf (GregoryPDE x) = ruleOf x

    indirectInference (GregoryPDE x) = indirectInference x 

    isAssumption (GregoryPDE x) = isAssumption x

    isPremise (GregoryPDE x) = isPremise x

    restriction (GregoryPDE x) = restriction x

parseGregoryPD rtc = map GregoryPD <$> (try (map PDtoPDE <$> quantRule) <|> try (parseEq) <|> liftProp)
    where liftProp = do r <- parseGregorySD (defaultRuntimeDeductionConfig)
                        return (map (PDtoPDE . SD . getGregorySD) r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "P", "A/EE", "Assumption"])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r `elem` ["A/EE"] -> return [SD (AS "/∃E")]
                              | r `elem` [ "P","Assumption"] -> return [Pr (problemPremises rtc)]
          parseEq = try (string "=E" >> return [IE1,IE2]) <|> (string "=I" >> return [II])

parseGregoryPDProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GregoryPD PureLexiconFOL (Form Bool)]
parseGregoryPDProof ders = toDeductionFitchAlt (parseGregoryPD ders) gregoryPDFormulaParser

parseGregoryPDE rtc = map GregoryPDE <$> (try liftPD <|> liftPDP)
    where liftPDP = map PDPtoPDEP <$> parseLogicBookPDPlus rtc
          liftPD = map (PDEtoPDEP . getGregoryPD) <$> parseGregoryPD rtc
          --XXX the confusing names here are because what Bergman calls
          --PDE, Gregory calls PD, and what Bergman calls PDEPlus, gregory calls
          --PDE

parseGregoryPDEProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GregoryPDE PureLexiconFOL (Form Bool)]
parseGregoryPDEProof ders = toDeductionFitchAlt (parseGregoryPDE ders) gregoryPDFormulaParser

gregoryNotation :: String -> String 
gregoryNotation x = case runParser altParser 0 "" x of
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

gregoryPDCalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parseGregoryPDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gregoryPDFormulaParser
    , ndParseForm = gregoryPDFormulaParser
    , ndNotation = gregoryNotation
    }

gregoryPDECalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parseGregoryPDEProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gregoryPDFormulaParser
    , ndParseForm = gregoryPDFormulaParser
    , ndNotation = gregoryNotation
    }
