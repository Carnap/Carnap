{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Paul
    (parsePaulSD, parsePaulSDE, paulSDCalc, paulSDECalc) where

import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson

parsePaulSD :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [LogicBookSD]
parsePaulSD rtc = do r <- choice (map (try . string) ["Assumption" ,"&I","/\\I", "∧I","&E","/\\E","∧E","CI","=>I", "->I","→I", ">I", "⊃I","→E", "⊃E","CE","->E"
                                                          , "→E", ">E" ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","|I","∨I", "vE","\\/E", "|E", "∨E","BI","<=>I","<>I","<->I"
                                                          , "↔I", "BE", "<->E","<>E", "<=>E", "↔E", "A","P", "R"]) <|> ((++) <$> string "A/" <*> many anyChar)
                     case r of
                            r | r `elem` ["A"] -> return [AS ""]
                              | r `elem` ["A/>I", "A/->I"] -> return [AS "/⊃I"]
                              | r `elem` ["A/=I"] -> return [AS "/≡I"]
                              | r `elem` ["P", "Assumption"] -> return [Pr (problemPremises rtc)]
                              | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                              | r `elem` ["&E","/\\E","∧E"] -> return [ConjElim1, ConjElim2]
                              | r `elem` ["CI","->I", "=>I","→I",">I", "⊃I"] -> return [CondIntro1,CondIntro2]
                              | r `elem` ["CE","->E","→E",">E", "⊃E"] -> return [CondElim]
                              | r `elem` ["~I","¬I","-I"]  -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                              | r `elem` ["~E","¬E","-E"]  -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                              | r `elem` ["vI","\\/I","|I","∨I"] -> return [DisjIntro1, DisjIntro2]
                              | r `elem` ["vE","\\/E","|E","∨E"] -> return [DisjElim1, DisjElim2,DisjElim3, DisjElim4]
                              | r `elem` ["BI","<->I","<>I","<=>I","↔I"] -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                              | r `elem` ["BE","<->E","<>E","<=>E","↔E"] -> return [BicoElim1, BicoElim2]
                            'A':'/':rest -> return [AS (" / " ++ rest)]
                            "R" -> return [Reiterate]

parsePaulSDE :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [LogicBookSDPlus]
parsePaulSDE rtc = try (map SD <$> parsePaulSD rtc) <|> parsePlus
    where parsePlus = do r <- choice (map (try . string) ["MT","HS","DS","Com","Assoc","Impl", "DN", "DeM", "Idem", "Trans", "Exp", "Dist", "Equiv"])
                         return $ case r of
                                    r | r == "MT" -> [MT]
                                      | r == "HS" -> [HS]
                                      | r == "DS" -> [DS1,DS2]
                                      | r == "Com" -> [Com1,Com2]
                                      | r == "Assoc" -> [Assoc1,Assoc2,Assoc3,Assoc4]
                                      | r == "Impl" -> [Impl1,Impl2]
                                      | r == "DN" -> [DN1, DN2]
                                      | r == "DeM" -> [DeM1,DeM2, DeM3, DeM4]
                                      | r == "Idem" -> [Idem1, Idem2, Idem3, Idem4]
                                      | r == "Trans" -> [Trans1, Trans2]
                                      | r == "Exp" -> [Exp1, Exp2]
                                      | r == "Dist" -> [Dist1, Dist2, Dist3, Dist4]
                                      | r == "Equiv" -> [Equiv1, Equiv2, Equiv3, Equiv4]

parsePaulSDProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine LogicBookSD PurePropLexicon (Form Bool)]
parsePaulSDProof ders = toDeductionFitchAlt (parsePaulSD ders) (purePropFormulaParser paulOpts)

parsePaulSDEProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine LogicBookSDPlus PurePropLexicon (Form Bool)]
parsePaulSDEProof ders = toDeductionFitchAlt (parsePaulSDE ders) (purePropFormulaParser paulOpts)

paulSDCalc = mkNDCalc 
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parsePaulSDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = extendedPropSeqParser
    , ndParseForm = purePropFormulaParser extendedLetters
    , ndNotation = dropOuterParens
    }

paulSDECalc = mkNDCalc 
    { ndRenderer = FitchStyle BergmanMooreAndNelsonStyle
    , ndParseProof = parsePaulSDEProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = extendedPropSeqParser
    , ndParseForm = purePropFormulaParser extendedLetters
    , ndNotation = dropOuterParens
    }
