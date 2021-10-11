{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Winkler
    ( parseWinklerTFL, winklerTFLCalc , winklerNotation, WinklerTFL(..)) where

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
from the Winkler Remix of Forall x book
-}

data WinklerTFL = ConjIntro  | As
                | ConjElim1  | ConjElim2
                | DisjIntro1 | DisjIntro2
                | DisjElim1  | DisjElim2
                | DisjElim3  | DisjElim4
                | CondIntro1 | CondIntro2
                | CondElim   | Reiterate  
                | BicoIntro1 | BicoIntro2
                | BicoIntro3 | BicoIntro4
                | BicoElim1  | BicoElim2
                | NegeIntro1 | NegeIntro2
                | NegeIntro3 | NegeIntro4
                | NegeIntro5 | NegeIntro6
                | NegeElim1  | NegeElim2
                | NegeElim3  | NegeElim4
                | NegeElim5  | NegeElim6
                | ContElim   | ContIntro
                | Tertium1   | Tertium2
                | Tertium3   | Tertium4
                | DisSyllo1  | DisSyllo2
                | ModTollens | DoubleNeg  
                | Com1 | Com2 
                | Assoc1 | Assoc2 | Assoc3 | Assoc4
                | Impl1 | Impl2
                | DN1  | DN2
                | DeM1 | DeM2 | DeM3 | DeM4
                | Idem1 | Idem2 | Idem3 | Idem4
                | Trans1 | Trans2
                | Exp1 | Exp2
                | Dist1 | Dist2 | Dist3 | Dist4
                | Equiv1 | Equiv2 | Equiv3 | Equiv4
                | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
                deriving (Eq)

instance Show WinklerTFL where
        show ConjIntro  = "&I"
        show ConjElim1  = "&E"
        show ConjElim2  = "&E"
        show NegeIntro1 = "~I"
        show NegeIntro2 = "~I"
        show NegeIntro3 = "~I"
        show NegeIntro4 = "~I"
        show NegeIntro5 = "~I"
        show NegeIntro6 = "~I"
        show NegeElim1  = "~E"
        show NegeElim2  = "~E"
        show NegeElim3  = "~E"
        show NegeElim4  = "~E"
        show NegeElim5  = "~E"
        show NegeElim6  = "~E"
        show CondIntro1 = "⊃I"
        show CondIntro2 = "⊃I"
        show CondElim   = "⊃E"
        show ContIntro  = "⊥I"
        show ContElim   = "X"
        show DisjElim1  = "∨E"
        show DisjElim2  = "∨E"
        show DisjElim3  = "∨E"
        show DisjElim4  = "∨E"
        show DisjIntro1 = "∨I"
        show DisjIntro2 = "∨I"
        show BicoIntro1 = "≡I"
        show BicoIntro2 = "≡I"
        show BicoIntro3 = "≡I"
        show BicoIntro4 = "≡I"
        show BicoElim1  = "≡E"
        show BicoElim2  = "≡E"
        show DisSyllo1  = "DS"
        show DisSyllo2  = "DS"
        show ModTollens = "MT"
        show DoubleNeg  = "DNE"
        show Tertium1   = "TND"
        show Tertium2   = "TND"
        show Tertium3   = "TND"
        show Tertium4   = "TND"
        show Com1       = "Com"
        show Com2       = "Com"
        show Assoc1     = "Assoc"
        show Assoc2     = "Assoc"
        show Assoc3     = "Assoc"
        show Assoc4     = "Assoc"
        show Impl1      = "Impl"
        show Impl2      = "Impl"
        show DN1        = "DN"
        show DN2        = "DN"
        show DeM1       = "DeM"
        show DeM2       = "DeM"
        show DeM3       = "DeM"
        show DeM4       = "DeM"
        show Idem1      = "Idem"
        show Idem2      = "Idem"
        show Idem3      = "Idem"
        show Idem4      = "Idem"
        show Trans1     = "Trans"
        show Trans2     = "Trans"
        show Exp1       = "Exp"
        show Exp2       = "Exp"
        show Dist1      = "Dist"
        show Dist2      = "Dist"
        show Dist3      = "Dist"
        show Dist4      = "Dist"
        show Equiv1     = "Equiv"
        show Equiv2     = "Equiv"
        show Equiv3     = "Equiv"
        show Equiv4     = "Equiv"
        show Reiterate  = "R"
        show As         = "AS"
        show (Pr _)     = "PR"

instance Inference WinklerTFL PurePropLexicon (Form Bool) where
        ruleOf ConjIntro  = adjunction
        ruleOf ConjElim1  = simplificationVariations !! 0
        ruleOf ConjElim2  = simplificationVariations !! 1
        ruleOf NegeIntro1 = constructiveReductioVariations !! 0
        ruleOf NegeIntro2 = constructiveReductioVariations !! 1
        ruleOf NegeIntro3 = constructiveReductioVariations !! 2
        ruleOf NegeIntro4 = constructiveReductioVariations !! 3
        ruleOf NegeIntro5 = constructiveFalsumReductioVariationsWithJunk !! 0
        ruleOf NegeIntro6 = constructiveFalsumReductioVariationsWithJunk !! 1
        ruleOf NegeElim1  = nonConstructiveReductioVariations !! 0
        ruleOf NegeElim2  = nonConstructiveReductioVariations !! 1
        ruleOf NegeElim3  = nonConstructiveReductioVariations !! 2
        ruleOf NegeElim4  = nonConstructiveReductioVariations !! 3
        ruleOf NegeElim5  = nonConstructiveFalsumReductioVariationsWithJunk !! 0
        ruleOf NegeElim6  = nonConstructiveFalsumReductioVariationsWithJunk !! 1
        ruleOf ContIntro  = falsumIntroduction
        ruleOf ContElim   = falsumElimination
        ruleOf CondIntro1 = conditionalProofVariations !! 0
        ruleOf CondIntro2 = conditionalProofVariations !! 1
        ruleOf CondElim   = modusPonens
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
        ruleOf DisSyllo1  = modusTollendoPonensVariations !! 0 
        ruleOf DisSyllo2  = modusTollendoPonensVariations !! 1
        ruleOf ModTollens = modusTollens
        ruleOf DoubleNeg  = doubleNegationElimination
        ruleOf Tertium1   = tertiumNonDaturVariations !! 0 
        ruleOf Tertium2   = tertiumNonDaturVariations !! 1
        ruleOf Tertium3   = tertiumNonDaturVariations !! 2
        ruleOf Tertium4   = tertiumNonDaturVariations !! 3
        ruleOf Reiterate  = identityRule
        ruleOf Com1   = andCommutativity !! 0
        ruleOf Com2   = orCommutativity !! 0
        ruleOf Assoc1 = andAssociativity !! 0
        ruleOf Assoc2 = andAssociativity !! 1
        ruleOf Assoc3 = orAssociativity !! 0
        ruleOf Assoc4 = orAssociativity !! 1
        ruleOf Impl1  = materialConditional !! 0
        ruleOf Impl2  = materialConditional !! 1
        ruleOf DN1    = doubleNegation !! 0
        ruleOf DN2    = doubleNegation !! 1
        ruleOf DeM1   = deMorgansLaws !! 0
        ruleOf DeM2   = deMorgansLaws !! 1
        ruleOf DeM3   = deMorgansLaws !! 2
        ruleOf DeM4   = deMorgansLaws !! 3
        ruleOf Idem1  = andIdempotence !! 0
        ruleOf Idem2  = andIdempotence !! 1
        ruleOf Idem3  = orIdempotence !! 0
        ruleOf Idem4  = orIdempotence !! 1
        ruleOf Trans1 = contraposition !! 0
        ruleOf Trans2 = contraposition !! 1
        ruleOf Exp1   = exportation !! 0
        ruleOf Exp2   = exportation !! 1
        ruleOf Dist1  = distribution !! 0
        ruleOf Dist2  = distribution !! 1
        ruleOf Dist3  = distribution !! 4
        ruleOf Dist4  = distribution !! 5
        ruleOf Equiv1 = biconditionalExchange !! 0
        ruleOf Equiv2 = biconditionalExchange !! 1
        ruleOf Equiv3 = biconditionalCases !! 0
        ruleOf Equiv4 = biconditionalCases !! 1
        ruleOf As         = axiom
        ruleOf (Pr _)     = axiom

        isAssumption As = True
        isAssumption _ = False

        isPremise (Pr _) = True
        isPremise _ = False

        indirectInference x
            | x `elem` [Tertium1,Tertium2,Tertium3,Tertium4] = Just (PolyTypedProof 2 (ProofType 1 1))
            | x `elem` [ NegeIntro1, NegeIntro2 , NegeIntro3, NegeIntro4, NegeIntro5, NegeIntro6
                       , NegeElim1, NegeElim2, NegeElim3 , NegeElim4, NegeElim5, NegeElim6
                       ] = Just (TypedProof (ProofType 0 2))
            | x `elem` [ DisjElim1, DisjElim2, DisjElim3, DisjElim4
                       , CondIntro1, CondIntro2 
                       , BicoIntro1, BicoIntro2 , BicoIntro3, BicoIntro4
                       ] = Just PolyProof
            | otherwise = Nothing

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

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
        globalRestriction (Left ded) n NegeIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeIntro3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeIntro4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeIntro5 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lfalsum])]
        globalRestriction (Left ded) n NegeIntro6 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lfalsum])]
        globalRestriction (Left ded) n NegeElim1  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n NegeElim2  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n NegeElim3  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n NegeElim4  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n NegeElim5 = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lfalsum])]
        globalRestriction (Left ded) n NegeElim6 = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lfalsum])]
        globalRestriction (Left ded) n Tertium1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
        globalRestriction (Left ded) n Tertium2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
        globalRestriction (Left ded) n Tertium3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
        globalRestriction (Left ded) n Tertium4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
        globalRestriction _ _ _ = Nothing

parseWinklerTFL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [WinklerTFL]
parseWinklerTFL rtc = do r <- choice (map (try . string) [ "&I", "&E", "-I", "~I", "-E", "~E", ">I", ">E", "⊃I", "⊃E", "!?I", "⊥I", "X"
                                                      , "\\/E", "\\/I", "vE", "vI", "∨E", "∨I", "<>I", "<>E","≡I", "≡E"
                                                      , "DS", "MT", "DNE", "TND", "Com", "Assoc", "Impl", "DN", "DeM"
                                                      , "Idem", "Trans", "Exp", "Dist", "Equiv", "R", "AS", "PR"])
                         return $ case r of
                           r | r == "&I" -> [ConjIntro]
                             | r == "&E" -> [ConjElim1, ConjElim2]
                             | r `elem` ["~I", "-I"] -> [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4, NegeIntro5, NegeIntro6]
                             | r `elem` ["~E", "-E"] -> [NegeElim1, NegeElim2, NegeElim3, NegeElim4, NegeElim5, NegeElim6]
                             | r `elem` [">I", "⊃I"] -> [CondIntro1, CondIntro2]
                             | r `elem` [">E", "⊃E"] -> [CondElim]
                             | r `elem` ["!?I", "⊥I"] -> [ContIntro]
                             | r == "X" -> [ContElim]
                             | r `elem` ["\\/E", "vE", "∨E"] -> [DisjElim1,DisjElim2,DisjElim3,DisjElim4]
                             | r `elem` ["\\/I", "vI", "∨I"] -> [DisjIntro1,DisjIntro2]
                             | r `elem` ["<>I", "≡I"] -> [BicoElim1,BicoElim2]     
                             | r `elem` ["<>E", "≡E"] -> [BicoIntro1,BicoIntro2,BicoIntro3,BicoIntro4] 
                             | r == "DS" -> [DisSyllo1, DisSyllo2]
                             | r == "MT" -> [ModTollens]
                             | r == "DNE" -> [DoubleNeg]
                             | r == "TND" -> [Tertium1,Tertium2,Tertium3,Tertium4] 
                             | r == "Com" -> [Com1,Com2]
                             | r == "Assoc" -> [Assoc1,Assoc2,Assoc3,Assoc4]
                             | r == "Impl" -> [Impl1,Impl2]
                             | r == "DN" -> [DN1,DN2]
                             | r == "DeM" -> [DeM1,DeM2,DeM3,DeM4]
                             | r == "Idem" -> [Idem1,Idem2,Idem3,Idem4]
                             | r == "Trans" -> [Trans1,Trans2]
                             | r == "Exp" -> [Exp1,Exp2]
                             | r == "Dist" -> [Dist1,Dist2,Dist3,Dist4]
                             | r == "Equiv" -> [Equiv1,Equiv2,Equiv3,Equiv4]
                             | r == "R" -> [Reiterate]
                             | r == "AS" -> [As]
                             | r == "PR" -> [Pr (problemPremises rtc)]

winklerNotation :: String -> String 
winklerNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleCon <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleCon = (char '∧' >> return "&") 
                      <|> (char '¬' >> return "~") 
                      <|> (char '→' >> return "⊃")
                      <|> (char '↔' >> return "≡")
                      <|> (char '⊤' >> return "")
          fallback = do c <- anyChar 
                        return [c]

parseWinklerTFLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine WinklerTFL PurePropLexicon (Form Bool)]
parseWinklerTFLProof rtc = toDeductionFitch (parseWinklerTFL rtc) langParser

winklerTFLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseWinklerTFLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver langParser
    , ndParseForm = langParser
    , ndNotation = winklerNotation
    }
