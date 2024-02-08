{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Raven
    ( parseRavenTFLCore, RavenTFLCore(..)
    , parseRavenTFL, RavenTFL(..)
    , ravenTFL2019Calc, ravenTFLCalc, ravenTFLCoreCalc
    , ravenNotation) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.Util.LanguageClasses

{-| A system for propositional logic resembling the basic proof system TFL
from the Calgary Remix of Forall x book
-}

data RavenTFLCore = ConjIntro  | As
                               | ConjElim1  | ConjElim2
                               | DisjIntro1 | DisjIntro2
                               | DisjElim1  | DisjElim2
                               | DisjElim3  | DisjElim4
                               | CondIntro1 | CondIntro2
                               | CondElim
                               | BicoIntro1 | BicoIntro2
                               | BicoIntro3 | BicoIntro4
                               | BicoElim1  | BicoElim2
                               | NegeIntro1 | NegeIntro2
                               | ContIntro   | ContElim 
                               | Indirect1  | Indirect2
                               | Reiterate
                               | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
                               deriving (Eq)

data RavenTFL = Core RavenTFLCore
                            | DisSyllo1  | DisSyllo2
                            | ModTollens | DoubleNeg  
                            | Lem1       | Lem2
                            | Lem3       | Lem4
                            | DeMorgan1  | DeMorgan2
                            | DeMorgan3  | DeMorgan4
                            deriving (Eq)
                            --skipping derived rules for now

instance Show RavenTFLCore where
        show ConjIntro  = "∧I"
        show ConjElim1  = "∧E"
        show ConjElim2  = "∧E"
        show NegeIntro1 = "¬I"
        show NegeIntro2 = "¬I"
        show ContIntro   = "⊥I"
        show Indirect1  = "¬E"
        show Indirect2  = "¬E"
        show CondIntro1 = "→I"
        show CondIntro2 = "→I"
        show CondElim   = "→E"
        show ContElim   = "⊥E"
        show DisjElim1  = "∨E"
        show DisjElim2  = "∨E"
        show DisjElim3  = "∨E"
        show DisjElim4  = "∨E"
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

instance Show RavenTFL where
        show (Core x)   = show x
        show DisSyllo1  = "DS"
        show DisSyllo2  = "DS"
        show ModTollens = "MT"
        show DoubleNeg  = "DNE"
        show Lem1       = "LEM"
        show Lem2       = "LEM"
        show Lem3       = "LEM"
        show Lem4       = "LEM"
        show DeMorgan1  = "DeM"
        show DeMorgan2  = "DeM"
        show DeMorgan3  = "DeM"
        show DeMorgan4  = "DeM"

instance Inference RavenTFLCore PurePropLexicon (Form Bool) where
        ruleOf ConjIntro  = adjunction
        ruleOf ConjElim1  = simplificationVariations !! 0
        ruleOf ConjElim2  = simplificationVariations !! 1
        ruleOf NegeIntro1 = constructiveFalsumReductioVariations !! 0
        ruleOf NegeIntro2 = constructiveFalsumReductioVariations !! 1
        ruleOf ContIntro   = falsumIntroduction
        ruleOf Indirect1  = nonConstructiveFalsumReductioVariations !! 0
        ruleOf Indirect2  = nonConstructiveFalsumReductioVariations !! 1
        ruleOf CondIntro1 = conditionalProofVariations !! 0
        ruleOf CondIntro2 = conditionalProofVariations !! 1
        ruleOf CondElim   = modusPonens
        ruleOf ContElim   = falsumElimination
        ruleOf DisjIntro1 = additionVariations !! 0
        ruleOf DisjIntro2 = additionVariations !! 1 
        ruleOf DisjElim1  = proofByCasesVariations !! 0
        ruleOf DisjElim2  = proofByCasesVariations !! 1
        ruleOf DisjElim3  = proofByCasesVariations !! 2
        ruleOf DisjElim4  = proofByCasesVariations !! 3
        ruleOf BicoIntro1 = biconditionalProofVariations !! 0
        ruleOf BicoIntro2 = biconditionalProofVariations !! 1
        ruleOf BicoIntro3 = biconditionalProofVariations !! 2
        ruleOf BicoIntro4 = biconditionalProofVariations !! 3
        ruleOf BicoElim1  = biconditionalPonensVariations !! 0
        ruleOf BicoElim2  = biconditionalPonensVariations !! 1
        ruleOf Reiterate  = identityRule
        ruleOf As         = axiom
        ruleOf (Pr _)     = axiom

        indirectInference x
            | x `elem` [ DisjElim1, DisjElim2, DisjElim3, DisjElim4
                       , CondIntro1, CondIntro2 , BicoIntro1, BicoIntro2
                       , BicoIntro3, BicoIntro4, NegeIntro1, NegeIntro2
                       , Indirect1, Indirect2 ] = Just PolyProof
            | otherwise = Nothing

        isAssumption As = True
        isAssumption _  = False

        isPremise (Pr _) = True
        isPremise _  = False

        globalRestriction (Left ded) n CondIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n CondIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n BicoIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n BicoIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n BicoIntro3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n BicoIntro4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n DisjElim1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n DisjElim2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n DisjElim3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n DisjElim4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n NegeIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n NegeIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n Indirect1 = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction (Left ded) n Indirect2 = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

instance Inference RavenTFL PurePropLexicon (Form Bool) where
        ruleOf (Core x)   = ruleOf x
        ruleOf DisSyllo1  = modusTollendoPonensVariations !! 0 
        ruleOf DisSyllo2  = modusTollendoPonensVariations !! 1
        ruleOf ModTollens = modusTollens
        ruleOf DoubleNeg  = doubleNegationElimination
        ruleOf Lem1       = tertiumNonDaturVariations !! 0 
        ruleOf Lem2       = tertiumNonDaturVariations !! 1
        ruleOf Lem3       = tertiumNonDaturVariations !! 2
        ruleOf Lem4       = tertiumNonDaturVariations !! 3
        ruleOf DeMorgan1  = deMorgansLaws !! 0
        ruleOf DeMorgan2  = deMorgansLaws !! 1
        ruleOf DeMorgan3  = deMorgansLaws !! 2
        ruleOf DeMorgan4  = deMorgansLaws !! 3

        indirectInference (Core x) = indirectInference x
        indirectInference x
            | x `elem` [Lem1,Lem2,Lem3,Lem4] = Just (PolyTypedProof 2 (ProofType 1 1))
            | otherwise = Nothing

        globalRestriction (Left ded) n (Core CondIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (Core CondIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (Core BicoIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core BicoIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core BicoIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core BicoIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core DisjElim1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core DisjElim2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core DisjElim3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core DisjElim4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core NegeIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (Core NegeIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (Core Indirect1) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction (Left ded) n (Core Indirect2) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

        isAssumption (Core x) = isAssumption x
        isAssumption _  = False

        isPremise (Core x) = isAssumption x
        isPremise _  = False

        restriction (Core x) = restriction x
        restriction _ = Nothing

parseRavenTFLCore :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [RavenTFLCore]
parseRavenTFLCore rtc = do r <- choice (map (try . string) [ "AS","PR"
                                                           , "&I","/\\I", "∧I"
                                                           , "&E","/\\E","∧E"
                                                           , "~I","-I", "¬I"
                                                           , "_|_I","!?I", "⊥I"
                                                           , "_|_E","!?E", "⊥E"
                                                           , "~E","-E", "¬E"
                                                           , "->I", ">I", "=>I" , "→I"
                                                           , "->E", ">E", "->E", "→E"
                                                           , "vI","\\/I", "|I", "∨I"
                                                           , "vE","\\/E", "|E", "∨E"
                                                           , "<->I", "↔I","<->E" , "↔E"
                                                           , "R"])
                           case r of
                               r | r == "AS"   -> return [As]
                                 | r == "PR" -> return [Pr (problemPremises rtc)]
                                 | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                                 | r `elem` ["&E","/\\E","∧E"] -> return [ConjElim1, ConjElim2]
                                 | r `elem` ["~I","¬I","-I"]   -> return [NegeIntro1, NegeIntro2]
                                 | r `elem` ["_|_I","!?I","⊥I"] -> return [ContIntro]
                                 | r `elem` ["_|_E","!?E","⊥E"] -> return [ContElim]
                                 | r `elem` ["~E","¬E","-E"] -> return [Indirect1, Indirect2]
                                 | r `elem` ["->I", ">I", "=>I", "→I"] -> return [CondIntro1,CondIntro2]
                                 | r `elem` ["->E", ">E", "=>E", "→E"]  -> return [CondElim]
                                 | r `elem` ["∨I","vI", "|I", "\\/I"] -> return [DisjIntro1, DisjIntro2]
                                 | r `elem` ["∨E","vE", "|E", "\\/E"] -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                 | r `elem` ["<->I","↔I"] -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                 | r `elem` ["<->E","↔E"]   -> return [BicoElim1, BicoElim2]
                                 | r == "R" -> return [Reiterate]

parseRavenTFL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [RavenTFL]
parseRavenTFL rtc = try parseExt <|> (map Core <$> parseRavenTFLCore rtc)
        where parseExt = do r <- choice (map (try . string) ["DS","MT","DNE","LEM","DeM"])
                            case r of
                               r | r == "DS"   -> return [DisSyllo1,DisSyllo2]
                                 | r == "MT"   -> return [ModTollens]
                                 | r == "DNE"  -> return [DoubleNeg]
                                 | r == "LEM"  -> return [Lem1,Lem2,Lem3,Lem4]
                                 | r == "DeM"   -> return [DeMorgan1,DeMorgan2,DeMorgan3,DeMorgan4]

parseRavenTFLCoreProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine RavenTFLCore PurePropLexicon (Form Bool)]
parseRavenTFLCoreProof rtc = toDeductionFitch (parseRavenTFLCore rtc) (purePropFormulaParser thomasBolducZachOpts) 

parseRavenTFLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine RavenTFL PurePropLexicon (Form Bool)]
parseRavenTFLProof rtc = toDeductionFitch (parseRavenTFL rtc) (purePropFormulaParser thomasBolducZachOpts)

parseRavenTFL2019Proof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine RavenTFLCore PurePropLexicon (Form Bool)]
parseRavenTFL2019Proof rtc = toDeductionFitch (parseRavenTFLCore rtc) (purePropFormulaParser thomasBolducZach2019Opts)

ravenNotation :: String -> String 
ravenNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          fallback = do c <- anyChar 
                        return [c]

ravenTFLCoreCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseRavenTFLCoreProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZachOpts)
    , ndParseForm = purePropFormulaParser thomasBolducZachOpts
    , ndNotation = ravenNotation
    }

ravenTFLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseRavenTFLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZachOpts)
    , ndParseForm = purePropFormulaParser thomasBolducZachOpts
    , ndNotation = dropOuterParens --to match the 2019 calc and make this basically a "Plus" version
    }

ravenTFL2019Calc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseRavenTFL2019Proof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZach2019Opts)
    , ndParseForm = purePropFormulaParser thomasBolducZach2019Opts
    , ndNotation = dropOuterParens
    }
