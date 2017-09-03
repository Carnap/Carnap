{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.ModalPropositional.Logic.Hardegree
    (parseHardegreeSL,  parseHardegreeSLProof, HardegreeSL, hardegreeSLCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Languages.ModalPropositional.Syntax
import Carnap.Languages.ModalPropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.ModalPropositional.Logic.Rules

--A system for propositional modal logic resembling the world-theory proof system from Gary
--Hardegree's Modal Logic

data HardegreeWTL = AndI | AndO1 | AndO2 | AndNI | AndNO
                 | OrI1 | OrI2  | OrO1  | OrO2  | OrNI  | OrNO
                 | IfI1 | IfI2  | IfO1  | IfO2  | IfNI  | IfNO
                 | IffI | IffO1 | IffO2 | IffNI | IffNO
                 | FalI | FalO  | FalNI | CD1   | CD2   | DD    
                 | ID1  | ID2   | ID3   | ID4   | AndD  | DN1 | DN2
                 | OrID Int 
                 | SepCases Int
                 | Pr | As | Rep
                 | WTZero1 | WTZero2 | WTNeg1 | WTNeg2 | WTAnd1 | WTAnd2 
                 | WTOr1 | WTOr2 | WTIf1 | WTIf2 | WTIff1 | WTIff2 
                 | WTAll1 | WTAll2 | WTSome1 | WTSome2 | WTNec1 | WTNec2 
                 | WTPos1 | WTPos2 | WTEG | WTUI | WTUG | WTED
               deriving (Eq)

instance Show HardegreeSL where
         show Pr     = "PR"
         show As     = "As"
         show Rep    = "Rep"
         show AndI   = "&I"  
         show AndO1  = "&O"
         show AndO2  = "&O"
         show AndNI  = "¬&I" 
         show AndNO  = "¬&O"
         show OrI1   = "∨I"
         show OrI2   = "∨I"
         show OrO1   = "∨O"
         show OrO2   = "∨O"
         show OrNI   = "¬∨I" 
         show OrNO   = "¬∨O"
         show IfI1   = "→I"
         show IfI2   = "→I"
         show IfO1   = "→O"
         show IfO2   = "→O"
         show IfNI   = "¬→I" 
         show IfNO   = "¬→O"
         show IffI   = "↔I"
         show IffO1  = "↔O"
         show IffO2  = "↔O"
         show IffNI  = "¬↔I" 
         show IffNO  = "¬↔O"
         show FalI   = "⊥I"
         show FalO   = "⊥O"
         show DN1    = "DN"
         show DN2    = "DN"
         show CD1    = "CD"
         show CD2    = "CD"
         show DD     = "DD"
         show ID1    = "ID"
         show ID2    = "ID"
         show ID3    = "ID"
         show ID4    = "ID"
         show AndD   = "&D"
         show (OrID n) = "∨ID" ++ show n
         show (SepCases n) = "SC" ++ show n
         show WTZero1 = "WT(0)
         show WTZero2 = "WT(0)"
         show WTNeg1 = "WT(¬)"
         show WTNeg2 = "WT(¬)"
         show WTAnd1 = "WT(&)"
         show WTAnd2 = "WT(&)"
         show WTOr1 = "WT(∨)"
         show WTOr2 = "WT(∨)"
         show WTIf1 = "WT(→)"
         show WTIf2 = "WT(→)"
         show WTIff1 = "WT(↔)"
         show WTIff2 = "WT(↔)"
         show WTAll1 = "WT(∀)"
         show WTAll2 = "WT(∀)"
         show WTSome1 = "WT(∃)"
         show WTSome2 = "WT(∃)"
         show WTNec1 = "WT(□)"
         show WTNec2 = "WT(□)"
         show WTPos1 = "WT(◇)"
         show WTPos2 = "WT(◇)"
         show WTEG = "∃I"
         show WTUI = "∀O"
         show WTUG = "UD"
         show WTED = "ED"

instance Inference HardegreeSL PurePropLexicon where
         ruleOf Pr       = axiom
         ruleOf As       = axiom
         ruleOf Rep      = identityRule
         ruleOf AndI     = adjunction
         ruleOf AndO1    = simplificationVariations !! 0
         ruleOf AndO2    = simplificationVariations !! 1
         ruleOf AndNI    = negatedConjunctionVariations !! 1
         ruleOf AndNO    = negatedConjunctionVariations !! 0
         ruleOf OrI1     = additionVariations !! 0
         ruleOf OrI2     = additionVariations !! 1
         ruleOf OrO1     = modusTollendoPonensVariations !! 0
         ruleOf OrO2     = modusTollendoPonensVariations !! 1
         ruleOf OrNI     = deMorgansNegatedOr !! 1
         ruleOf OrNO     = deMorgansNegatedOr !! 0
         ruleOf IfI1     = materialConditionalVariations !! 0
         ruleOf IfI2     = materialConditionalVariations !! 1
         ruleOf IfO1     = modusPonens
         ruleOf IfO2     = modusTollens
         ruleOf IfNI     = negatedConditionalVariations !! 1
         ruleOf IfNO     = negatedConditionalVariations !! 0
         ruleOf IffI     = conditionalToBiconditional
         ruleOf IffO1    = biconditionalToConditionalVariations !! 0
         ruleOf IffO2    = biconditionalToConditionalVariations !! 1
         ruleOf IffNI    = negatedBiconditionalVariations !! 1
         ruleOf IffNO    = negatedBiconditionalVariations !! 0
         ruleOf FalI     = falsumIntroduction
         ruleOf FalO     = falsumElimination
         ruleOf DN1      = doubleNegationIntroduction
         ruleOf DN2      = doubleNegationElimination
         ruleOf CD1      = explicitConditionalProofVariations !! 0
         ruleOf CD2      = explicitConditionalProofVariations !! 1
         ruleOf DD       = identityRule
         ruleOf ID1      = explicitConstructiveFalsumReductioVariations !! 0
         ruleOf ID2      = explicitConstructiveFalsumReductioVariations !! 1
         ruleOf ID3      = explicitNonConstructiveFalsumReductioVariations !! 0
         ruleOf ID4      = explicitNonConstructiveFalsumReductioVariations !! 1
         ruleOf AndD     = adjunction
         ruleOf (OrID n) = eliminationOfCases n
         ruleOf (SepCases n) = separationOfCases n
         ruleOf WTZero1 = worldTheoryZeroAxiom
         ruleOf WTZero2 = worldTheoryZeroAxiom
         ruleOf WTNeg1 = worldTheoryNegAxiom
         ruleOf WTNeg2 = worldTheoryNegAxiom
         ruleOf WTAnd1 = worldTheoryAndAxiom
         ruleOf WTAnd2 = worldTheoryAndAxiom
         ruleOf WTOr1 = worldTheoryOrAxiom
         ruleOf WTOr2 = worldThoeryOrAxiom
         ruleOf WTIf1 = worldTheoryIfAxiom
         ruleOf WTIf2 = worldTheoryIfAxiom
         ruleOf WTIff1 = worldTheoryIffAxiom
         ruleOf WTIff2 = worldTheoryIffAxiom
         ruleOf WTAll1 = worldTheoryAllAxiom
         ruleOf WTAll2 = worldTheoryAllAxiom
         ruleOf WTSome1 = worldTheorySomeAxiom
         ruleOf WTSome2 = worldTheorySomeAxiom
         ruleOf WTNec1 = worldTheoryNecAxiom
         ruleOf WTNec2 = worldTheoryNecAxiom
         ruleOf WTPos1 = worldTheoryPosAxiom
         ruleOf WTPos2 = worldTheoryPosAxiom
         ruleOf WTEG = worldTheoryExistentialGeneralization 
         ruleOf WTUI = worldTheoryUniversalInstantiation
         ruleOf WTUG = worldTheoryUniversalGeneralization
         ruleOf WTED = worldTheoryExistentialDerivation

         -- TODO fix this up so that these rules use ProofTypes with variable
         -- arities.
         indirectInference (SepCases n) = Just (TypedProof (ProofType 0 n))
         indirectInference (OrID n) = Just (TypedProof (ProofType n 1))
         indirectInference (AndD) = Just doubleProof
         indirectInference DD = Just (TypedProof (ProofType 0 1))
         indirectInference ED = Just (TypedProof (ProofType 1 1))
         indirectInference x 
            | x `elem` [ID1,ID2,ID3,ID4,CD1,CD2] = Just assumptiveProof
            | otherwise = Nothing

         isAssumption As = True
         isAssumption _ = False

parseHardegreeSL :: Map String DerivedRule -> Parsec String u [HardegreeSL]
parseHardegreeSL ders = do r <- choice (map (try . string) ["AS","PR","&I","&O","~&I","~&O","->I","->O","~->I","~->O","→I","→O","~→I","~→O","!?I"
                                                           ,"!?O","vID","\\/ID","vI","vO","~vI","~vO","\\/I","\\/O","~\\/I","~\\/O","<->I","<->O","~<->I"
                                                           ,"~<->O","↔I","↔O","~↔I","~↔O","ID","&D","SC","DN","DD","CD","REP", 
                                                           , "WT(0)", "WT(~)", "WT(/\\)", "WT(&)", "WT(\\/)", "WT(v)", "WT(->)", "WT(<->)", 
                                                           , "WT(A)", "WT(E)", "WT([])", "WT(<>)", "EI", "AO", "UD" , "ED"
                                                           ])
                           case r of
                             "AS"    -> return [As]
                             "PR"    -> return [Pr]
                             "REP"   -> return [Rep]
                             "&I"    -> return [AndI]
                             "&O"    -> return [AndO1,AndO2]
                             "~&I"   -> return [AndNI]
                             "~&O"   -> return [AndNO]
                             "->I"   -> return [IfI1,IfO2]
                             "->O"   -> return [IfO1,IfO2]
                             "~->I"  -> return [IfNI]
                             "~->O"  -> return [IfNO]
                             "→I"    -> return [IfO1,IffO2]           
                             "→O"    -> return [IfI1,IfO2]          
                             "~→I"   -> return [IfNI]
                             "~→O"   -> return [IfNO]
                             "!?I"   -> return [FalI]
                             "!?O"   -> return [FalO]
                             "vI"    -> return [OrI1, OrI2]
                             "vO"    -> return [OrO1, OrO2]
                             "~vI"   -> return [OrNI]
                             "~vO"   -> return [OrNO]
                             "\\/I"  -> return [OrI1, OrI2] 
                             "\\/O"  -> return [OrO1, OrO2]
                             "~\\/I" -> return [OrNI]
                             "~\\/O" -> return [OrNO]
                             "<->I"  -> return [IffI]       
                             "<->O"  -> return [IffO1,IffO2]
                             "~<->I" -> return [IffNI]       
                             "~<->O" -> return [IffNO]
                             "↔I"    -> return [IffI]       
                             "↔O"    -> return [IffO1,IffO2]
                             "~↔I"   -> return [IffNI]       
                             "~↔O"   -> return [IffNO]
                             "ID"    -> return [ID1,ID2,ID3,ID4]
                             "DN"    -> return [DN1,DN2]
                             "&D"    -> return [AndD]
                             "DD"    -> return [DD]
                             "CD"    -> return [CD1,CD2]
                             "WT(0)" -> return [WTZero1,WTZero2]
                             "WT(~)" -> return [WTNeg1,WTNeg2]
                             "WT(/\\)" -> return [WTAnd1, WTAnd2]
                             "WT(&)"   -> return [WTAnd1, WTAnd2]
                             "WT(\\/)" -> return [WTOr1, WTOr2]
                             "WT(v)"   -> return [WTOr1, WTOr2]
                             "WT(->)"  -> return [WTIf1, WTIf2]
                             "WT(<->)" -> return [WTIff1, WTIff2]
                             "WT(A)"   -> return [WTAll1, WTAll2]
                             "WT(E)"   -> return [WTSome1, WTSome2]
                             "WT([])"  -> return [WTNeg1, WTNec2]
                             "WT(<>)"  -> return [WTPos1, WTPos2]
                             "EI"      -> return [WTEG]
                             "AO"      -> return [WTUI]
                             "UD"      -> return [WTUD]
                             "SC"    -> do ds <- many1 digit
                                           return [SepCases (read ds)]
                             "\\/ID" -> do ds <- many1 digit
                                           return [OrID (read ds)]
                             "vID"   -> do ds <- many1 digit
                                           return [OrID (read ds)]

parseHardegreeWTLProof :: Map String DerivedRule -> String -> [DeductionLine HardegreeSL PurePropLexicon (Form Bool)]
parseHardegreeWTLProof ders = toDeductionHardegree null worldTheoryPropFormulaParser

hardegreeWTLCalc = NaturalDeductionCalc 
    { ndRenderer = MontegueStyle
    , ndParseProof = parseHardegreeWTLProof
    , ndProcessLine = processLineHardegree
    , ndProcessLineMemo = Nothing
    , ndParseSeq = worldTheorySeqParser
    }
