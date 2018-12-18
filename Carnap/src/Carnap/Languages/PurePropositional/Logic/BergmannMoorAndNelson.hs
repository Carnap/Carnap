{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.BergmannMoorAndNelson
    (parseLogicBookSD, parseLogicBookSDProof, LogicBookSD,
     logicBookSDCalc, parseLogicBookSDPlus, parseLogicBookSDPlusProof, LogicBookSDPlus,
     logicBookSDPlusCalc) where

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


--A system for propositional logic resembling the proof system SD from
--Bergmann, Moor and Nelson's Logic Book

data LogicBookSD = ConjIntro  
                        | ConjElim1  | ConjElim2
                        | CondIntro1 | CondIntro2
                        | CondElim
                        | NegeIntro1 | NegeIntro2
                        | NegeIntro3 | NegeIntro4
                        | NegeElim1  | NegeElim2
                        | NegeElim3  | NegeElim4
                        | DisjIntro1 | DisjIntro2
                        | DisjElim1  | DisjElim2
                        | DisjElim3  | DisjElim4
                        | BicoIntro1 | BicoIntro2 
                        | BicoIntro3 | BicoIntro4
                        | BicoElim1  | BicoElim2
                        | Reiterate  | LBAS
                        | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               deriving Eq

instance Show LogicBookSD where
        show ConjIntro  = "&I"
        show ConjElim1  = "&E"
        show ConjElim2  = "&E"
        show CondIntro1 = "⊃I"
        show CondIntro2 = "⊃I"
        show CondElim   = "⊃E"
        show NegeIntro1 = "~I"
        show NegeIntro2 = "~I"
        show NegeIntro3 = "~I"
        show NegeIntro4 = "~I"
        show NegeElim1  = "~E" 
        show NegeElim2  = "~E"
        show NegeElim3  = "~E"
        show NegeElim4  = "~E"
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
        show Reiterate  = "R"
        show (Pr _)     = "PR"
        show LBAS       = "AS"

instance Inference LogicBookSD PurePropLexicon (Form Bool) where
    ruleOf Reiterate  = identityRule
    ruleOf CondElim   = modusPonens
    ruleOf CondIntro1 = conditionalProofVariations !! 0 
    ruleOf CondIntro2 = conditionalProofVariations !! 1
    ruleOf ConjIntro  = adjunction
    ruleOf NegeIntro1 = constructiveReductioVariations !! 0
    ruleOf NegeIntro2 = constructiveReductioVariations !! 1
    ruleOf NegeIntro3 = constructiveReductioVariations !! 2
    ruleOf NegeIntro4 = constructiveReductioVariations !! 3
    ruleOf NegeElim1  = nonConstructiveReductioVariations !! 0
    ruleOf NegeElim2  = nonConstructiveReductioVariations !! 1
    ruleOf NegeElim3  = nonConstructiveReductioVariations !! 2
    ruleOf NegeElim4  = nonConstructiveReductioVariations !! 3
    ruleOf DisjIntro1 = additionVariations !! 0
    ruleOf DisjIntro2 = additionVariations !! 1
    ruleOf DisjElim1  = proofByCasesVariations !! 0
    ruleOf DisjElim2  = proofByCasesVariations !! 1
    ruleOf DisjElim3  = proofByCasesVariations !! 2
    ruleOf DisjElim4  = proofByCasesVariations !! 3
    ruleOf ConjElim1  = simplificationVariations !! 0
    ruleOf ConjElim2  = simplificationVariations !! 1
    ruleOf BicoIntro1 = biconditionalProofVariations !! 0
    ruleOf BicoIntro2 = biconditionalProofVariations !! 1
    ruleOf BicoIntro3 = biconditionalProofVariations !! 2
    ruleOf BicoIntro4 = biconditionalProofVariations !! 3
    ruleOf (Pr _)     = axiom
    ruleOf LBAS       = axiom
    ruleOf BicoElim1  = biconditionalPonensVariations !! 0
    ruleOf BicoElim2  = biconditionalPonensVariations !! 1

    indirectInference x
        | x `elem` [CondIntro1,CondIntro2, BicoIntro1, BicoIntro2
                   , BicoIntro3, BicoIntro4 , DisjElim1, DisjElim2
                   , DisjElim3, DisjElim4 ] = Just PolyProof
        | x `elem` [ NegeIntro1, NegeIntro2 , NegeIntro3, NegeIntro4
                   , NegeElim1, NegeElim2, NegeElim3, NegeElim4
                   ] = Just doubleProof
        | otherwise = Nothing

    isAssumption LBAS = True
    isAssumption _ = False

    restriction (Pr prems) = Just (premConstraint prems)
    restriction _ = Nothing

parseLogicBookSD :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [LogicBookSD]
parseLogicBookSD rtc = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I", "⊃I","→E", "⊃E","CE","->E"
                                                          , "→E" ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I"
                                                          , "≡I" , "BE", "<->E", "↔E", "≡E", "R"])
                          case r of
                            r | r == "AS" -> return [LBAS]
                              | r == "PR" -> return [Pr (problemPremises rtc)]
                              | r == "R"    -> return [Reiterate]
                              | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                              | r `elem` ["&E","/\\E","∧E"] -> return [ConjElim1, ConjElim2]
                              | r `elem` ["CI","->I","→I","⊃I"] -> return [CondIntro1,CondIntro2]
                              | r `elem` ["CE","->E","→E","⊃E"] -> return [CondElim]
                              | r `elem` ["~I","¬I","-I"]  -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                              | r `elem` ["~E","¬E","-E"]  -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                              | r `elem` ["vI","\\/I"] -> return [DisjIntro1, DisjIntro2]
                              | r `elem` ["vE","\\/E"] -> return [DisjElim1, DisjElim2,DisjElim3, DisjElim4]
                              | r `elem` ["BI","<->I","↔I","≡I"] -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                              | r `elem` ["BE","<->E","↔E","≡E"] -> return [BicoElim1, BicoElim2]

parseLogicBookSDProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine LogicBookSD PurePropLexicon (Form Bool)]
parseLogicBookSDProof ders = toDeductionFitch (parseLogicBookSD ders) (purePropFormulaParser extendedLetters)

logicBookSDCalc = mkNDCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseLogicBookSDPlusProof
    , ndProcessLine = processLineFitch
    , ndProcessLineMemo = Nothing
    , ndParseSeq = extendedPropSeqParser
    }

data LogicBookSDPlus = SD LogicBookSD | MT | HS 
                     | DS1  | DS2 
                     | Com1 | Com2 | Com3 | Com4
                     | Assoc1 | Assoc2 | Assoc3 | Assoc4
                     | Impl1 | Impl2
                     | DN1  | DN2
                     | DeM1 | DeM2 | DeM3 | DeM4
                     | Idem1 | Idem2 | Idem3 | Idem4
                     | Trans1 | Trans2
                     | Exp1 | Exp2
                     | Dist1 | Dist2 | Dist3 | Dist4
                     | Equiv1 | Equiv2 | Equiv3 | Equiv4

instance Show LogicBookSDPlus where
        show (SD x) = show x
        show MT = "MT"
        show HS = "HS"
        show DS1 = "DS"
        show DS2 = "DS"
        show Com1 = "Com"
        show Com2 = "Com"
        show Assoc1 = "Assoc"
        show Assoc2 = "Assoc"
        show Assoc3 = "Assoc"
        show Assoc4 = "Assoc"
        show Impl1 = "Impl"
        show Impl2 = "Impl"
        show DN1 = "DN"
        show DN2 = "DN"
        show DeM1 = "DeM"
        show DeM2 = "DeM"
        show DeM3 = "DeM"
        show DeM4 = "DeM"
        show Idem1 = "Idem"
        show Idem2 = "Idem"
        show Idem3 = "Idem"
        show Idem4 = "Idem"
        show Trans1 = "Trans"
        show Trans2 = "Trans"
        show Exp1 = "Exp"
        show Exp2 = "Exp"
        show Dist1 = "Dist"
        show Dist2 = "Dist"
        show Dist3 = "Dist"
        show Dist4 = "Dist"
        show Equiv1 = "Equiv"
        show Equiv2 = "Equiv"
        show Equiv3 = "Equiv"
        show Equiv4 = "Equiv"

instance Inference LogicBookSDPlus PurePropLexicon (Form Bool) where
    ruleOf (SD r) = ruleOf r
    ruleOf MT = modusTollens
    ruleOf HS = hypotheticalSyllogism
    ruleOf DS1 = modusTollendoPonensVariations !! 0
    ruleOf DS2 = modusTollendoPonensVariations !! 1
    ruleOf Com1 = andCommutativity !! 0
    ruleOf Com2 = orCommutativity !! 0
    ruleOf Assoc1 = andAssociativity !! 0
    ruleOf Assoc2 = andAssociativity !! 1 
    ruleOf Assoc3 = orAssociativity !! 0  
    ruleOf Assoc4 = orAssociativity !! 1  
    ruleOf Impl1 = materialConditional !! 0
    ruleOf Impl2 = materialConditional !! 1
    ruleOf DN1 = doubleNegation !! 0
    ruleOf DN2 = doubleNegation !! 1
    ruleOf DeM1 = deMorgansLaws !! 0 
    ruleOf DeM2 = deMorgansLaws !! 1
    ruleOf DeM3 = deMorgansLaws !! 2
    ruleOf DeM4 = deMorgansLaws !! 3
    ruleOf Idem1 = andIdempotence !! 0
    ruleOf Idem2 = andIdempotence !! 1
    ruleOf Idem3 = orIdempotence !! 0
    ruleOf Idem4 = orIdempotence !! 1
    ruleOf Trans1 = contraposition !! 0
    ruleOf Trans2 = contraposition !! 1
    ruleOf Exp1 = exportation !! 0
    ruleOf Exp2 = exportation !! 1
    ruleOf Dist1 = distribution !! 0
    ruleOf Dist2 = distribution !! 1
    ruleOf Dist3 = distribution !! 2
    ruleOf Dist4 = distribution !! 3
    ruleOf Equiv1 = biconditionalExchange !! 0
    ruleOf Equiv2 = biconditionalExchange !! 1
    ruleOf Equiv3 = biconditionalCases !! 0
    ruleOf Equiv4 = biconditionalCases !! 1

    indirectInference (SD x) = indirectInference x
    indirectInference _ = Nothing

    isAssumption (SD x) = isAssumption x
    isAssumption _ = False

    restriction (SD x ) = restriction x
    restriction _ = Nothing

parseLogicBookSDPlus :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [LogicBookSDPlus]
parseLogicBookSDPlus rtc = try (map SD <$> parseLogicBookSD rtc) <|> parsePlus
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

parseLogicBookSDPlusProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine LogicBookSDPlus PurePropLexicon (Form Bool)]
parseLogicBookSDPlusProof ders = toCommentedDeductionFitch (parseLogicBookSDPlus ders) (purePropFormulaParser extendedLetters)

logicBookSDPlusCalc = mkNDCalc 
    { ndRenderer = FitchStyle
    , ndParseProof = parseLogicBookSDPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = extendedPropSeqParser
    }
