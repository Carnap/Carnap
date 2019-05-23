{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
    ( parseIchikawaJenkinsSL, IchikawaJenkinsSL,  ichikawaJenkinsSLCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

newtype IchikawaJenkinsSL = IJ MagnusSLPlus
    deriving Eq

instance Show IchikawaJenkinsSL where
        show (IJ (MSL CondIntro1)) = "⊃I"
        show (IJ (MSL CondIntro2)) = "⊃I"
        show (IJ (MSL CondElim))   = "⊃E"
        show (IJ (MSL BicoIntro1)) = "≡I"
        show (IJ (MSL BicoIntro2)) = "≡I"
        show (IJ (MSL BicoIntro3)) = "≡I"
        show (IJ (MSL BicoIntro4)) = "≡I"
        show (IJ (MSL BicoElim1))  = "≡E"
        show (IJ (MSL BicoElim2))  = "≡E"
        show (IJ BiExRep) = "≡ex"
        show (IJ RepBiEx) = "≡ex"
        show (IJ x) = show x

instance Inference IchikawaJenkinsSL PurePropLexicon (Form Bool) where
        ruleOf (IJ (MSL BicoIntro1)) = biconditionalProofVariations !! 0
        ruleOf (IJ (MSL BicoIntro2)) = biconditionalProofVariations !! 1
        ruleOf (IJ (MSL BicoIntro3)) = biconditionalProofVariations !! 2
        ruleOf (IJ (MSL BicoIntro4)) = biconditionalProofVariations !! 3
        ruleOf (IJ x) = ruleOf x

        indirectInference (IJ (MSL x)) 
            | x `elem` [ BicoIntro1, BicoIntro2
                       , BicoIntro3, BicoIntro4] = Just PolyProof
        indirectInference (IJ (MSL x)) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (IJ x) = isAssumption x
        isAssumption _ = False

        isPremise (IJ x) = isPremise x
        isPremise _ = False

        restriction (IJ x) = restriction x
        restriction _ = Nothing

parseIchikawaJenkinsSL :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [IchikawaJenkinsSL]
parseIchikawaJenkinsSL rtc = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI",">I","->I","⊃I","→E","CE",">E", "->E", "⊃E"
                                                         ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<>I","<->I", "≡I" 
                                                         , "BE", "<>E","<->E", "≡E", "R", "HYP","DIL","MT", "Comm", "DN", "MC", "≡ex", "<>ex", "<->ex", "DeM"])
                                                         <|> ((++) <$> string "A/" <*> many anyChar)
                                case r of
                                 r | r == "AS" -> fromMSL [As ""]
                                   | r == "PR" -> fromMSL [Pr (problemPremises rtc)]
                                   | r == "R"  -> fromMSL [Reiterate]
                                   | r `elem` ["&I","/\\I","∧I"] -> fromMSL [ConjIntro]
                                   | r `elem` ["&E","/\\E","∧E"] -> fromMSL [ConjElim1, ConjElim2]
                                   | r `elem` ["CI",">I", "->I","⊃I"]  -> fromMSL [CondIntro1,CondIntro2]
                                   | r `elem` ["CE",">E", "->E", "⊃E"] -> fromMSL [CondElim]
                                   | r `elem` ["~I","¬I","-I"]   -> fromMSL [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                                   | r `elem` ["~E","¬E","-E"]   -> fromMSL [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                                   | r `elem` ["vI","\\/I"]   -> fromMSL [DisjIntro1, DisjIntro2]
                                   | r `elem` ["vE","\\/E"]   -> fromMSL [DisjElim1, DisjElim2]
                                   | r `elem` ["BI","<>I","<->I","≡I"]   -> fromMSL [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                   | r `elem` ["BE","<>E","<->E","≡E"] -> fromMSL [BicoElim1, BicoElim2]
                                   | r == "HYP"  -> fromMSLPlus [Hyp]
                                   | r == "DIL"   -> fromMSLPlus [Dilemma]
                                   | r == "Comm"  -> fromMSLPlus [AndComm,CommAnd,OrComm,CommOr,IffComm,CommIff]
                                   | r == "DN"    -> fromMSLPlus [DNRep,RepDN]
                                   | r == "MC"    -> fromMSLPlus [MCRep,MCRep2,RepMC,RepMC2]
                                   | r `elem` ["≡ex", "<>ex", "<->ex"] -> fromMSLPlus [BiExRep,RepBiEx]
                                   | r == "DeM"   -> fromMSLPlus [DM1,DM2,DM3,DM4]
                                 'A':'/':rest -> fromMSL [As rest]
    where fromMSL = return . map (IJ . MSL)
          fromMSLPlus = return . map IJ

parseIchikawaJenkinsProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine IchikawaJenkinsSL PurePropLexicon (Form Bool)]
parseIchikawaJenkinsProof rtc = toDeductionFitch (parseIchikawaJenkinsSL rtc) (purePropFormulaParser magnusOpts)

ichikawaJenkinsNotation :: String -> String 
ichikawaJenkinsNotation x = case runParser altparser 0 "" x of
                                    Left e -> show e
                                    Right s -> s
    where altparser = do s <- handlecon <|> try handleatom <|> handleLParen <|> handleRParen <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handlecon = (char '∧' >> return "&") 
                      <|> (char '→' >> return "⊃")
                      <|> (char '↔' >> return "≡")
          handleatom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          handleLParen = do char '('
                            n <- getState 
                            putState (n + 1)
                            return $ ["(","["] !! (n `mod` 2) 
          handleRParen = do char ')'
                            n <- getState 
                            putState (n - 1)
                            return $ [")","]"] !! ((n - 1) `mod` 2)
          fallback = do c <- anyChar 
                        return [c]

ichikawaJenkinsSLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseIchikawaJenkinsProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser magnusOpts)
    , ndParseForm = purePropFormulaParser magnusOpts
    , ndNotation = ichikawaJenkinsNotation
    }
