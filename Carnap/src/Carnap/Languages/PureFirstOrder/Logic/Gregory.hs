{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gregory where

import Text.Parsec
import Data.List (intercalate)
import Carnap.Core.Data.Types (Form, Term)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Gregory hiding (GregorySDE(..))
import Carnap.Languages.PurePropositional.Logic.Gregory (GregorySDE(GregorySDE))
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson hiding (SD,Pr)
import Carnap.Languages.PurePropositional.Logic.Rules (doubleNegatingModusTollensVariations, doubleNegatingModusTollendoPonensVariations)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PureFirstOrder.Logic.BergmannMoorAndNelson
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PureFirstOrder.Util

newtype GregoryPD = GregoryPD { getGregoryPD :: LogicBookPDE }

data GregoryPDE = GregoryPDE { getGregoryPDE :: LogicBookPDEPlus }
                | GregoryMT1
                | GregoryMT2
                | GregoryMT3
                | GregoryDS1
                | GregoryDS2
                | GregoryDeM1
                | GregoryDeM2
                | GregoryDeM3
                | GregoryDeM4
                | GregoryDeM5
                | GregoryDeM6
                | GregoryDeM7
                | GregoryDeM8
                | GregoryDeM9
                | GregoryDeM10
                | GregoryDeM11
                | GregoryDeM12
                | GregoryTrans1
                | GregoryTrans2
                | GregoryTrans3
                | GregoryTrans4
                | GregoryImpl1
                | GregoryImpl2
                | GregoryQN1
                | GregoryQN2
                | GregoryQN3
                | GregoryQN4

instance Show GregoryPD where
    show (GregoryPD (PDtoPDE (SD x))) = show (GregorySD x)
    show (GregoryPD (PDtoPDE (Pr _))) = "P"
    show (GregoryPD x) = show x

instance Show GregoryPDE where
    show (GregoryPDE (PDPtoPDEP (SDPlus x))) = show (GregorySDE x)
    show (GregoryPDE (PDPtoPDEP (PDtoPDP x))) = show (GregoryPD (PDtoPDE x))
    show (GregoryPDE (PDEtoPDEP x)) = show (GregoryPD x)
    show GregoryQN1 = "QN"
    show GregoryQN2 = "QN"
    show GregoryQN3 = "QN"
    show GregoryQN4 = "QN"
    show GregoryMT1 = "MT"
    show GregoryMT2 = "MT"
    show GregoryMT3 = "MT"
    show GregoryDS1 = "DS"
    show GregoryDS2 = "DS"
    show GregoryDeM1 = "DeM"
    show GregoryDeM2 = "DeM"
    show GregoryDeM3 = "DeM"
    show GregoryDeM4 = "DeM"
    show GregoryDeM5 = "DeM"
    show GregoryDeM6 = "DeM"
    show GregoryDeM7 = "DeM"
    show GregoryDeM8 = "DeM"
    show GregoryDeM9 = "DeM"
    show GregoryDeM10 = "DeM"
    show GregoryDeM11 = "DeM"
    show GregoryDeM12 = "DeM"
    show GregoryTrans1 = "Trans"
    show GregoryTrans2 = "Trans"
    show GregoryTrans3 = "Trans"
    show GregoryTrans4 = "Trans"
    show GregoryImpl1 = "Impl"
    show GregoryImpl2 = "Impl"
    show (GregoryPDE x) = show x

instance Inference GregoryPD PureLexiconFOL (Form Bool) where
    ruleOf (GregoryPD x) = ruleOf x

    indirectInference (GregoryPD x) = indirectInference x 

    isAssumption (GregoryPD x) = isAssumption x

    isPremise (GregoryPD x) = isPremise x

    restriction (GregoryPD x) = restriction x

instance Inference GregoryPDE PureLexiconFOL (Form Bool) where

    ruleOf GregoryMT1 = doubleNegatingModusTollensVariations !! 0
    ruleOf GregoryMT2 = doubleNegatingModusTollensVariations !! 1
    ruleOf GregoryMT3 = doubleNegatingModusTollensVariations !! 2
    ruleOf GregoryDS1 = doubleNegatingModusTollendoPonensVariations !! 0
    ruleOf GregoryDS2 = doubleNegatingModusTollendoPonensVariations !! 1
    ruleOf GregoryDeM1 = doubleNegatingDeMorgansLaws !! 0
    ruleOf GregoryDeM2 = doubleNegatingDeMorgansLaws !! 1
    ruleOf GregoryDeM3 = doubleNegatingDeMorgansLaws !! 2
    ruleOf GregoryDeM4 = doubleNegatingDeMorgansLaws !! 3
    ruleOf GregoryDeM5 = doubleNegatingDeMorgansLaws !! 4
    ruleOf GregoryDeM6 = doubleNegatingDeMorgansLaws !! 5
    ruleOf GregoryDeM7 = doubleNegatingDeMorgansLaws !! 6
    ruleOf GregoryDeM8 = doubleNegatingDeMorgansLaws !! 7
    ruleOf GregoryDeM9 = doubleNegatingDeMorgansLaws !! 8
    ruleOf GregoryDeM10 = doubleNegatingDeMorgansLaws !! 9
    ruleOf GregoryDeM11 = doubleNegatingDeMorgansLaws !! 10
    ruleOf GregoryDeM12 = doubleNegatingDeMorgansLaws !! 11
    ruleOf GregoryTrans1 = doubleNegatingContraposition !! 0
    ruleOf GregoryTrans2 = doubleNegatingContraposition !! 1
    ruleOf GregoryTrans3 = doubleNegatingContraposition !! 2
    ruleOf GregoryTrans4 = doubleNegatingContraposition !! 3
    ruleOf GregoryImpl1 = materialConditional !! 2
    ruleOf GregoryImpl2 = materialConditional !! 3
    ruleOf (GregoryQN1) = quantifierDoubleNegationReplace !! 0
    ruleOf (GregoryQN2) = quantifierDoubleNegationReplace !! 1
    ruleOf (GregoryQN3) = quantifierDoubleNegationReplace !! 2
    ruleOf (GregoryQN4) = quantifierDoubleNegationReplace !! 3
    ruleOf (GregoryPDE x) = ruleOf x

    indirectInference (GregoryPDE x) = indirectInference x 
    indirectInference _ = Nothing

    isAssumption (GregoryPDE x) = isAssumption x
    isAssumption _ = False

    isPremise (GregoryPDE x) = isPremise x
    isPremise _ = False

    restriction (GregoryPDE x) = restriction x
    restriction _ = Nothing

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

parseGregoryPDE rtc = handleQN <|> parsePlus <|> map GregoryPDE <$> (try liftPD <|> liftPDP)
    where liftPDP = map PDPtoPDEP <$> parseLogicBookPDPlus rtc
          liftPD = map (PDEtoPDEP . getGregoryPD) <$> parseGregoryPD rtc
          handleQN = string "QN" >> return (map (GregoryPDE . PDPtoPDEP) [QN1, QN2, QN3, QN4] ++ [GregoryQN1, GregoryQN2, GregoryQN3, GregoryQN4])
          parsePlus = do r <- choice (map (try . string) ["MT", "DS", "Trans", "Impl", "DeM"])
                         return $ case r of
                            r | r == "MT" -> [constructPlus MT, GregoryMT1, GregoryMT2, GregoryMT3]
                              | r == "DeM" -> [ constructPlus DeM1, constructPlus DeM2, constructPlus DeM3, constructPlus DeM4
                                              , GregoryDeM1, GregoryDeM2, GregoryDeM3, GregoryDeM4
                                              , GregoryDeM5, GregoryDeM6, GregoryDeM7, GregoryDeM8
                                              , GregoryDeM9, GregoryDeM10 , GregoryDeM11, GregoryDeM12
                                              ]
                              | r == "DS" -> [constructPlus DS1, constructPlus DS2, GregoryDS1, GregoryDS2]
                              | r == "Trans" -> [constructPlus Trans1, constructPlus Trans2, GregoryTrans1, GregoryTrans2, GregoryTrans3, GregoryTrans4]
                              | r == "Impl" -> [constructPlus Impl1, constructPlus Impl2, GregoryImpl1, GregoryImpl2]
          constructPlus = GregoryPDE . PDPtoPDEP . SDPlus
          --XXX the confusing names here are because what Bergman calls
          --PDE, Gregory calls PD, and what Bergman calls PDEPlus, gregory calls
          --PDE

parseGregoryPDEProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GregoryPDE PureLexiconFOL (Form Bool)]
parseGregoryPDEProof ders = toDeductionFitchAlt (parseGregoryPDE ders) gregoryPDFormulaParser

gregoryNotation :: String -> String 
gregoryNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleCon <|> try handleQuant <|> try handleAtom <|> try handleIneq <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleCon = (char '⊤' >> return " ")
                  <|> (char '∅' >> return " ")
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
          handleIneq = do char '¬'
                          c1 <- handleTerm
                          char '='
                          c2 <- handleTerm
                          return (c1 ++ "≠" ++ c2)
          fallback = do c <- anyChar 
                        return [c]

gregoryPDCalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parseGregoryPDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gregoryPDFormulaParser
    , ndParseForm = gregoryPDFormulaParser
    , ndNotation = dropOuterParens . gregoryNotation
    }

gregoryPDECalc = mkNDCalc
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parseGregoryPDEProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gregoryPDFormulaParser
    , ndParseForm = gregoryPDFormulaParser
    , ndNotation = dropOuterParens . gregoryNotation
    }
