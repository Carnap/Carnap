{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Hardegree
    (parseHardegreeSL,  parseHardegreeSLProof, HardegreeSL, hardegreeSLCalc, hardegreeNotation) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules

--A system for propositional logic resembling the proof system from Gary
--Hardegree's Modal Logic

data HardegreeSL = AndI | AndO1 | AndO2 | AndNI | AndNO
                 | OrI1 | OrI2  | OrO1  | OrO2  | OrNI  | OrNO
                 | IfI1 | IfI2  | IfO1  | IfO2  | IfNI  | IfNO
                 | IffI | IffO1 | IffO2 | IffNI | IffNO
                 | FalI | FalO  | FalNI | CD1   | CD2   | DD    
                 | ID1  | ID2   | ID3   | ID4   | AndD  | DN1 | DN2
                 | OrID Int | SepCases Int |  As | Rep
                 | PR (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               deriving (Eq)

instance Show HardegreeSL where
         show (PR _) = "PR"
         show As     = "As"
         show Rep    = "Rep"
         show AndI   = "&I"  
         show AndO1  = "&O"
         show AndO2  = "&O"
         show AndNI  = "~&I" 
         show AndNO  = "~&O"
         show OrI1   = "∨I"
         show OrI2   = "∨I"
         show OrO1   = "∨O"
         show OrO2   = "∨O"
         show OrNI   = "~∨I" 
         show OrNO   = "~∨O"
         show IfI1   = "→I"
         show IfI2   = "→I"
         show IfO1   = "→O"
         show IfO2   = "→O"
         show IfNI   = "~→I" 
         show IfNO   = "~→O"
         show IffI   = "↔I"
         show IffO1  = "↔O"
         show IffO2  = "↔O"
         show IffNI  = "~↔I" 
         show IffNO  = "~↔O"
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

instance Inference HardegreeSL PurePropLexicon (Form Bool) where
         ruleOf (PR _)   = axiom
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

         -- TODO fix this up so that these rules use ProofTypes with variable
         -- arities.
         indirectInference (SepCases n) = Just (TypedProof (ProofType 0 n))
         indirectInference (OrID n) = Just (TypedProof (ProofType n 1))
         indirectInference (AndD) = Just doubleProof
         indirectInference DD = Just (TypedProof (ProofType 0 1))
         indirectInference x 
            | x `elem` [ID1,ID2,ID3,ID4,CD1,CD2] = Just assumptiveProof
            | otherwise = Nothing

         isAssumption As = True
         isAssumption _ = False

         restriction (PR prems) = Just (premConstraint prems)
         restriction _ = Nothing

parseHardegreeSL :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [HardegreeSL]
parseHardegreeSL rtc = do r <- choice (map (try . string) ["AS","PR","&I","&O","~&I","~&O","/\\I","/\\O","~/\\I","~/\\O","->I","->O","~->I","~->O","→I","→O","~→I","~→O","!?I"
                                                          ,"!?O","vID","\\/ID","vI","vO","~vI","~vO","\\/I","\\/O","~\\/I","~\\/O","<->I","<->O","~<->I"
                                                          ,"~<->O","↔I","↔O","~↔I","~↔O","ID","&D","SC","DN","DD","CD","REP"
                                                          ])
                          case r of
                               r | r == "AS" -> return [As]
                                 | r == "PR" -> return [PR (problemPremises rtc)]
                                 | r == "REP" -> return [Rep]
                                 | r `elem` ["&I","/\\I"] -> return [AndI]
                                 | r `elem` ["&O","/\\O"]  -> return [AndO1,AndO2]
                                 | r `elem` ["~&I","~/\\I"] -> return [AndNI]
                                 | r `elem` ["~&O","~/\\O"] -> return [AndNO]
                                 | r `elem` ["->I","→I"]    -> return [IfI1,IfI2]           
                                 | r `elem` ["->O","→O"]    -> return [IfO1,IfO2]          
                                 | r `elem` ["~→I","~->I"]  -> return [IfNI]
                                 | r `elem` ["~->O","~→O"]   -> return [IfNO]
                                 | r == "!?I" -> return [FalI]
                                 | r == "!?O" -> return [FalO]
                                 | r `elem` ["vI","\\/I"]  -> return [OrI1, OrI2] 
                                 | r `elem` ["vO","\\/O"]  -> return [OrO1, OrO2]
                                 | r `elem` ["~vI","~\\/I"] -> return [OrNI]
                                 | r `elem` ["~vO","~\\/O"] -> return [OrNO]
                                 | r `elem` ["<->I","↔I"]    -> return [IffI]       
                                 | r `elem` ["<->O","↔O"]    -> return [IffO1,IffO2]
                                 | r `elem` ["~<->I","~↔I"]   -> return [IffNI]       
                                 | r `elem` ["~<->O","~↔O"]   -> return [IffNO]
                                 | r == "ID" -> return [ID1,ID2,ID3,ID4]
                                 | r == "DN" -> return [DN1,DN2]
                                 | r == "&D" -> return [AndD]
                                 | r == "DD"    -> return [DD]
                                 | r == "CD"    -> return [CD1,CD2]
                                 | r == "SC" -> do ds <- many1 digit
                                                   return [SepCases (read ds)]
                                 | r `elem` ["\\/ID","vID"] -> do ds <- many1 digit
                                                                  return [OrID (read ds)]

parseHardegreeSLProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine HardegreeSL PurePropLexicon (Form Bool)]
parseHardegreeSLProof rtc = toDeductionHardegree (parseHardegreeSL rtc) (purePropFormulaParser hardegreeOpts)

hardegreeNotation = map fixSym . dropOuterParens 
    where fixSym '∧' = '&'
          fixSym '¬' = '~'
          fixSym '⊥' = '⨳'
          fixSym x = x

hardegreeSLCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseHardegreeSLProof
    , ndProcessLine = processLineHardegree
    , ndProcessLineMemo = Nothing
    , ndNotation  = hardegreeNotation
    , ndParseSeq = parseSeqOver (purePropFormulaParser hardegreeOpts)
    , ndParseForm = purePropFormulaParser hardegreeOpts
    }
