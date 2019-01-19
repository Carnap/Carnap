{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Magnus
    ( parseMagnusSL, parseMagnusSLPlus, MagnusSLPlus, magnusSLPlusCalc, MagnusSL,  magnusSLCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

{-| A system for propositional logic resembling the basic proof system SL
from PD Magnus' forallx book
-}

data MagnusSL = Reiterate  | ConjIntro
              | ConjElim1  | ConjElim2
              | DisjIntro1 | DisjIntro2
              | DisjElim1  | DisjElim2
              | CondIntro1 | CondIntro2
              | CondElim
              | BicoIntro1 | BicoIntro2
              | BicoIntro3 | BicoIntro4
              | BicoElim1  | BicoElim2
              | NegeIntro1 | NegeIntro2
              | NegeIntro3 | NegeIntro4
              | NegeElim1  | NegeElim2
              | NegeElim3  | NegeElim4
              | As         
              | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
              deriving (Eq)
              --skipping derived rules for now

instance Show MagnusSL where
        show ConjIntro  = "∧I"
        show ConjElim1  = "∧E"
        show ConjElim2  = "∧E"
        show CondIntro1 = "→I"
        show CondIntro2 = "→I"
        show CondElim   = "→E"
        show NegeIntro1 = "¬I"
        show NegeIntro2 = "¬I"
        show NegeIntro3 = "¬I"
        show NegeIntro4 = "¬I"
        show NegeElim1  = "¬E" 
        show NegeElim2  = "¬E"
        show NegeElim3  = "¬E"
        show NegeElim4  = "¬E"
        show DisjElim1  = "∨E"
        show DisjElim2  = "∨E"
        show DisjIntro1 = "∨I"
        show DisjIntro2 = "∨I"
        show BicoIntro1 = "↔I"
        show BicoIntro2 = "↔I"
        show BicoIntro3 = "↔I"
        show BicoIntro4 = "↔I"
        show BicoElim1  = "↔E"
        show BicoElim2  = "↔E"
        show Reiterate  = "R"
        show As         = "AS"
        show (Pr _)     = "PR"

instance Inference MagnusSL PurePropLexicon (Form Bool) where
        ruleOf Reiterate  = identityRule
        ruleOf ConjIntro  = adjunction
        ruleOf ConjElim1  = simplificationVariations !! 0
        ruleOf ConjElim2  = simplificationVariations !! 1
        ruleOf DisjIntro1 = additionVariations !! 0
        ruleOf DisjIntro2 = additionVariations !! 1 
        ruleOf DisjElim1  = modusTollendoPonensVariations !! 0
        ruleOf DisjElim2  = modusTollendoPonensVariations !! 1
        ruleOf CondIntro1 = conditionalProofVariations !! 0
        ruleOf CondIntro2 = conditionalProofVariations !! 1
        ruleOf CondElim   = modusPonens
        ruleOf BicoIntro1 = biconditionalProofVariations !! 0
        ruleOf BicoIntro2 = biconditionalProofVariations !! 1
        ruleOf BicoIntro3 = biconditionalProofVariations !! 2
        ruleOf BicoIntro4 = biconditionalProofVariations !! 3
        ruleOf BicoElim1  = biconditionalPonensVariations !! 0
        ruleOf BicoElim2  = biconditionalPonensVariations !! 1
        ruleOf NegeIntro1 = constructiveReductioVariations !! 0
        ruleOf NegeIntro2 = constructiveReductioVariations !! 1
        ruleOf NegeIntro3 = constructiveReductioVariations !! 2
        ruleOf NegeIntro4 = constructiveReductioVariations !! 3
        ruleOf NegeElim1  = nonConstructiveReductioVariations !! 0
        ruleOf NegeElim2  = nonConstructiveReductioVariations !! 1
        ruleOf NegeElim3  = nonConstructiveReductioVariations !! 2
        ruleOf NegeElim4  = nonConstructiveReductioVariations !! 3
        ruleOf As         = axiom
        ruleOf (Pr _)     = axiom

        indirectInference x
            | x `elem` [CondIntro1,CondIntro2, BicoIntro1, BicoIntro2
                       , BicoIntro3, BicoIntro4 ] = Just PolyProof
            | x `elem` [ NegeIntro1, NegeIntro2 , NegeIntro3, NegeIntro4
                       , NegeElim1, NegeElim2, NegeElim3 , NegeElim4
                       ] = Just doubleProof
            | otherwise = Nothing

        isAssumption As = True
        isAssumption _ = False

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

parseMagnusSL :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [MagnusSL]
parseMagnusSL rtc = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I","→E","CE","->E", "→E"
                                                         ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I" 
                                                         , "BE", "<->E", "↔E", "R"])
                       case r of
                            r | r == "AS" -> return [As]
                              | r == "PR" -> return [Pr (problemPremises rtc)]
                              | r == "R"  -> return [Reiterate]
                              | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                              | r `elem` ["&E","/\\E","∧E"] -> return [ConjElim1, ConjElim2]
                              | r `elem` ["CI","->I","→I"]  -> return [CondIntro1,CondIntro2]
                              | r `elem` ["CE","->E", "→E"] -> return [CondElim]
                              | r `elem` ["~I","¬I","-I"]   -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                              | r `elem` ["~E","¬E","-E"]   -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                              | r `elem` ["vI","\\/I"]   -> return [DisjIntro1, DisjIntro2]
                              | r `elem` ["vE","\\/E"]   -> return [DisjElim1, DisjElim2]
                              | r `elem` ["BI","<->I","↔I"]   -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                              | r `elem` ["BE","<->E","↔E"] -> return [BicoElim1, BicoElim2]

parseMagnusSLProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine MagnusSL PurePropLexicon (Form Bool)]
parseMagnusSLProof rtc = toDeductionFitch (parseMagnusSL rtc) (purePropFormulaParser magnusOpts)

magnusNotation :: String -> String 
magnusNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> s
    where altparser = do s <- handlecon <|> try handleatom <|> handleLParen <|> handleRParen <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handlecon = char '∧' >> return "&"
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

magnusSLCalc = mkNDCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseMagnusSLProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Nothing
    , ndParseSeq = parseSeqOver (purePropFormulaParser magnusOpts)
    , ndNotation = magnusNotation
    }

{-| A system for propositional logic resembling the proof system SL
from PD Magnus' forallx book, including the derived and replacement rules
-}
data MagnusSLPlus = MSL MagnusSL | Hyp 
                  | Dilemma      | MT
                  --various replacement rules with their reverse
                  --directions included
                  | AndComm      | CommAnd 
                  | OrComm       | CommOr
                  | IffComm      | CommIff
                  | DNRep        | RepDN
                  | MCRep        | RepMC
                  | MCRep2       | RepMC2
                  | BiExRep      | RepBiEx
                  --plus DeMorgans
                  | DM1 | DM2 | DM3 | DM4

instance Show MagnusSLPlus where
        show (MSL x) = show x
        show Hyp     = "HS"
        show MT      = "MT"
        show Dilemma = "DIL"
        show AndComm = "Comm"
        show CommAnd = "Comm"
        show OrComm  = "Comm"
        show CommOr  = "Comm"
        show IffComm = "Comm"
        show CommIff = "Comm"
        show DNRep   = "DN"
        show RepDN   = "DN"
        show MCRep   = "MC"
        show RepMC   = "MC"
        show MCRep2  = "MC"
        show RepMC2  = "MC"
        show BiExRep = "↔ex"
        show RepBiEx = "↔ex"
        show DM1     = "DeM"
        show DM2     = "DeM"
        show DM3     = "DeM"
        show DM4     = "DeM"

instance Inference MagnusSLPlus PurePropLexicon (Form Bool) where
        ruleOf (MSL x) = ruleOf x
        ruleOf Hyp     = hypotheticalSyllogism
        ruleOf MT      = modusTollens
        ruleOf Dilemma = dilemma
        ruleOf AndComm = andCommutativity !! 0
        ruleOf CommAnd = andCommutativity !! 1
        ruleOf OrComm  = orCommutativity !! 0
        ruleOf CommOr  = orCommutativity !! 1
        ruleOf IffComm = iffCommutativity !! 0 
        ruleOf CommIff = iffCommutativity !! 1
        ruleOf DNRep   = doubleNegation !! 0
        ruleOf RepDN   = doubleNegation !! 1
        ruleOf MCRep   = materialConditional !! 0
        ruleOf RepMC   = materialConditional !! 1
        ruleOf MCRep2  = materialConditional !! 2
        ruleOf RepMC2  = materialConditional !! 3
        ruleOf BiExRep = biconditionalExchange !! 1
        ruleOf RepBiEx = biconditionalExchange !! 2
        ruleOf DM1    = deMorgansLaws !! 0
        ruleOf DM2    = deMorgansLaws !! 1
        ruleOf DM3    = deMorgansLaws !! 2
        ruleOf DM4    = deMorgansLaws !! 3

        indirectInference (MSL x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (MSL x) = isAssumption x
        isAssumption _ = False

        restriction (MSL x) = restriction x
        restriction _ = Nothing

parseMagnusSLPlus :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [MagnusSLPlus]
parseMagnusSLPlus rtc = try plus <|> basic 
    where basic = map MSL <$> parseMagnusSL rtc
          plus = do r <- choice (map (try . string) ["HYP","DIL","MT", "Comm", "DN", "MC", "↔ex", "<->ex", "DeM"])
                    case r of
                        "HYP"   -> return [Hyp]
                        "DIL"   -> return [Dilemma]
                        "Comm"  -> return [AndComm,CommAnd,OrComm,CommOr,IffComm,CommIff]
                        "DN"    -> return [DNRep,RepDN]
                        "MC"    -> return [MCRep,MCRep2,RepMC,RepMC2]
                        "↔ex"   -> return [BiExRep,RepBiEx]
                        "<->ex" -> return [BiExRep,RepBiEx]
                        "DeM"   -> return [DM1,DM2,DM3,DM4]

parseMagnusSLPlusProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine MagnusSLPlus PurePropLexicon (Form Bool)]
parseMagnusSLPlusProof rtc = toDeductionFitch (parseMagnusSLPlus rtc) (purePropFormulaParser magnusOpts)

magnusSLPlusCalc = mkNDCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseMagnusSLPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser magnusOpts)
    , ndNotation = magnusNotation
    }

