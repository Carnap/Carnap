{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Hardegree
    (parseHardegreeSL, parseHardegreeSL2006, parseHardegreeSLProof, HardegreeSL2006, HardegreeSL, hardegreeSL2006Calc, hardegreeSLCalc, hardegreeNotation) where

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

--A system for propositional logic resembling the proof system from Gary
--Hardegree's Modal Logic

data HardegreeSL = AndI | AndO1 | AndO2 | AndNI | AndNO | AndD 
                 | OrI1 | OrI2  | OrO1  | OrO2  | OrNI  | OrNO | OrID Int 
                 | IfI1 | IfI2  | IfO1  | IfO2  | IfNI  | IfNO | CD1 | CD2
                 | IffI | IffO1 | IffO2 | IffNI | IffNO | IffD
                 | FalI | FalO  | FalNI
                 | DN1  | DN2   | ID1 | ID2 | TD1  | TD2
                 | SepCases Int | As  | Rep | DD
                 | PR (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               deriving (Eq)

--A system for propositional logic resembling the proof system from Gary
--Hardegree's First Course book
data HardegreeSL2006 = HardegreeSL2006 HardegreeSL | OrNO2 | OrD1 | OrD2 
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
         show IffD  = "↔D"
         show FalI   = "⨳I"
         show FalO   = "⨳O"
         show DN1    = "DN"
         show DN2    = "DN"
         show CD1    = "CD"
         show CD2    = "CD"
         show DD     = "DD"
         show ID1    = "ID"
         show ID2    = "ID"
         show TD1    = "~D"
         show TD2    = "~D"
         show AndD   = "&D"
         show (OrID n) = "∨D" ++ show n
         show (SepCases n) = "SC" ++ show n

instance Show HardegreeSL2006 where
        show OrD1 = "∨D"
        show OrD2 = "∨D"
        show OrNO2 = "~∨O"
        show (HardegreeSL2006 x) = show x

instance Inference HardegreeSL PurePropLexicon (Form Bool) where
         ruleOf AndI     = adjunction
         ruleOf AndO1    = simplificationVariations !! 0
         ruleOf AndO2    = simplificationVariations !! 1
         ruleOf AndNI    = negatedConjunctionVariations !! 1
         ruleOf AndNO    = negatedConjunctionVariations !! 0
         ruleOf AndD     = adjunction
         ruleOf OrI1     = additionVariations !! 0
         ruleOf OrI2     = additionVariations !! 1
         ruleOf OrO1     = modusTollendoPonensVariations !! 0
         ruleOf OrO2     = modusTollendoPonensVariations !! 1
         ruleOf OrNI     = deMorgansNegatedOr !! 1
         ruleOf OrNO     = deMorgansNegatedOr !! 0
         ruleOf (OrID n) = eliminationOfCases n
         ruleOf IfI1     = materialConditionalVariations !! 0
         ruleOf IfI2     = materialConditionalVariations !! 1
         ruleOf IfO1     = modusPonens
         ruleOf IfO2     = modusTollens
         ruleOf IfNI     = negatedConditionalVariations !! 1
         ruleOf IfNO     = negatedConditionalVariations !! 0
         ruleOf CD1      = explicitConditionalProofVariations !! 0
         ruleOf CD2      = explicitConditionalProofVariations !! 1
         ruleOf IffI     = conditionalToBiconditional
         ruleOf IffO1    = biconditionalToConditionalVariations !! 0
         ruleOf IffO2    = biconditionalToConditionalVariations !! 1
         ruleOf IffNI    = negatedBiconditionalVariations !! 1
         ruleOf IffNO    = negatedBiconditionalVariations !! 0
         ruleOf IffD     = conditionalToBiconditional
         ruleOf FalI     = falsumIntroduction
         ruleOf FalO     = falsumElimination
         ruleOf DN1      = doubleNegationIntroduction
         ruleOf DN2      = doubleNegationElimination
         ruleOf TD1      = explicitConstructiveFalsumReductioVariations !! 0
         ruleOf TD2      = explicitConstructiveFalsumReductioVariations !! 1
         ruleOf ID1      = explicitNonConstructiveFalsumReductioVariations !! 0
         ruleOf ID2      = explicitNonConstructiveFalsumReductioVariations !! 1
         ruleOf (PR _)   = axiom
         ruleOf As       = axiom
         ruleOf Rep      = identityRule
         ruleOf DD       = identityRule
         ruleOf (SepCases n) = separationOfCases n

         -- TODO fix this up so that these rules use ProofTypes with variable
         -- arities.
         indirectInference (SepCases n) = Just (TypedProof (ProofType 0 n))
         indirectInference (OrID n) = Just (TypedProof (ProofType n 1))
         indirectInference AndD = Just doubleProof
         indirectInference IffD = Just doubleProof
         indirectInference DD = Just (TypedProof (ProofType 0 1))
         indirectInference x 
            | x `elem` [ID1,ID2,TD1,TD2,CD1,CD2] = Just assumptiveProof
            | otherwise = Nothing

         isAssumption As = True
         isAssumption _ = False

         restriction (PR prems) = Just (premConstraint prems)
         restriction _ = Nothing

instance Inference HardegreeSL2006 PurePropLexicon (Form Bool) where

         ruleOf (HardegreeSL2006 OrNO) = negatedDisjunctionVariations !! 0
         ruleOf OrNO2 = negatedDisjunctionVariations !! 1
         ruleOf OrD1 = explicitNonConstructiveFalsumReductioVariations !! 0
         ruleOf OrD2 = explicitNonConstructiveFalsumReductioVariations !! 1
         ruleOf (HardegreeSL2006 x) = ruleOf x

         indirectInference (HardegreeSL2006 x) = indirectInference x
         indirectInference OrD1 = Just assumptiveProof
         indirectInference OrD2 = Just assumptiveProof
         indirectInference _ = Nothing

         isAssumption (HardegreeSL2006 x) = isAssumption x
         isAssumption _ = False

         restriction (HardegreeSL2006 x) = restriction x
         restriction _ = Nothing

parseHardegreeSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [HardegreeSL]
parseHardegreeSL rtc = do r <- choice (map (try . string) ["&I","&O","~&I","~&O", "&D"
                                                          ,"->I","→I" ,"->O","→O","~->I","~→I","~->O","~→O", "CD"
                                                          ,"∨I","vI","\\/I","∨O","vO","\\/O","~∨I", "~vI","~\\/I","~∨O","~vO","~\\/O", "∨D", "vD","\\/D"
                                                          ,"<->I","↔I","<->O","↔O","~<->I","~↔I","~<->O","~↔O", "<->D", "↔D"
                                                          ,"!?I" ,"!?O", "ID", "~D","SC","DN","DD","REP","AS","PR"
                                                          ])
                          case r of
                               r | r == "AS" -> return [As]
                                 | r == "PR" -> return [PR (problemPremises rtc)]
                                 | r == "REP" -> return [Rep]
                                 | r `elem` ["&I"] -> return [AndI]
                                 | r `elem` ["&O"] -> return [AndO1,AndO2]
                                 | r `elem` ["~&I"] -> return [AndNI]
                                 | r `elem` ["~&O"] -> return [AndNO]
                                 | r `elem` ["->I","→I"] -> return [IfI1,IfI2]
                                 | r `elem` ["->O","→O"] -> return [IfO1,IfO2]
                                 | r `elem` ["~→I","~->I"] -> return [IfNI]
                                 | r `elem` ["~->O","~→O"] -> return [IfNO]
                                 | r == "!?I" -> return [FalI]
                                 | r == "!?O" -> return [FalO]
                                 | r `elem` ["∨I","vI","\\/I"] -> return [OrI1, OrI2]
                                 | r `elem` ["∨O","vO","\\/O"] -> return [OrO1, OrO2]
                                 | r `elem` ["~∨I", "~vI","~\\/I"] -> return [OrNI]
                                 | r `elem` ["~∨O", "~vO","~\\/O"] -> return [OrNO]
                                 | r `elem` ["<->I","↔I"] -> return [IffI]
                                 | r `elem` ["<->O","↔O"] -> return [IffO1,IffO2]
                                 | r `elem` ["~<->I","~↔I"] -> return [IffNI]
                                 | r `elem` ["~<->O","~↔O"] -> return [IffNO]
                                 | r `elem` ["<->D","↔D"] -> return [IffD]
                                 | r == "ID" -> return [ID1,ID2]
                                 | r == "~D" -> return [TD1,TD2]
                                 | r == "DN" -> return [DN1,DN2]
                                 | r == "&D" -> return [AndD]
                                 | r == "DD" -> return [DD]
                                 | r == "CD" -> return [CD1,CD2]
                                 | r == "SC" -> do ds <- many1 digit
                                                   return [SepCases (read ds)]
                                 | r `elem` ["∨D","\\/D","vD"] -> do ds <- many1 digit
                                                                     return [OrID (read ds)]

parseHardegreeSL2006 :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [HardegreeSL2006]
parseHardegreeSL2006 rtc = try new <|> (map HardegreeSL2006 <$> core) 
    where new = do r <- choice (map (try . string) ["∨D", "vD", "\\/D", "~\\/O", "~∨O", "~vO"])
                   return $ case r of
                       r | r `elem` ["∨D", "vD", "\\/D"] -> [OrD1, OrD2]
                         | r `elem` ["~\\/O", "~∨O", "~vO"] -> [HardegreeSL2006 OrNO, OrNO2]
          core = do r <- choice (map (try . string) ["&I","&O","~&O", "&D"
                                                    ,"->O","→O","~->O","~→O", "CD"
                                                    ,"∨I","vI","\\/I","∨O","vO","\\/O"
                                                    ,"<->I","↔I","<->O","↔O","~<->O","~↔O", "<->D", "↔D"
                                                    ,"!?I" ,"!?O", "ID", "~D","SC","DN","DD","REP","AS","PR"
                                                    ])
                    return $ case r of
                         r | r == "AS" -> [As]
                           | r == "PR" -> [PR (problemPremises rtc)]
                           | r == "REP" -> [Rep]
                           | r `elem` ["&I"] -> [AndI]
                           | r `elem` ["&O"]  -> [AndO1,AndO2]
                           | r `elem` ["~&O"] -> [AndNO]
                           | r `elem` ["->O","→O"] -> [IfO1,IfO2]
                           | r `elem` ["~->O","~→O"] -> [IfNO]
                           | r == "!?I" -> [FalI]
                           | r == "!?O" -> [FalO]
                           | r `elem` ["∨I", "vI","\\/I"] -> [OrI1, OrI2]
                           | r `elem` ["∨O", "vO","\\/O"] -> [OrO1, OrO2]
                           | r `elem` ["~∨O", "~vO","~\\/O"] -> [OrNO]
                           | r `elem` ["<->I","↔I"] -> [IffI]
                           | r `elem` ["<->O","↔O"] -> [IffO1,IffO2]
                           | r `elem` ["~<->O","~↔O"] -> [IffNO]
                           | r `elem` ["<->D","↔D"] -> [IffD]
                           | r == "ID" -> [ID1,ID2,TD1,TD2] 
                           --TD1,TD2 aren't actually forms of ID according
                           --to 2006 rule sheet, but are used as such in
                           --the book. Accomodating that seems the option
                           --least likely to confuse.
                           | r == "~D" -> [TD1,TD2]
                           | r == "DN" -> [DN1,DN2]
                           | r == "&D" -> [AndD]
                           | r == "DD" -> [DD]
                           | r == "CD" -> [CD1,CD2]

parseHardegreeSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine HardegreeSL PurePropLexicon (Form Bool)]
parseHardegreeSLProof rtc = toDeductionHardegree (parseHardegreeSL rtc) (purePropFormulaParser hardegreeOpts)

parseHardegreeSL2006Proof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine HardegreeSL2006 PurePropLexicon (Form Bool)]
parseHardegreeSL2006Proof rtc = toDeductionHardegree (parseHardegreeSL2006 rtc) (purePropFormulaParser hardegreeOpts)

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

hardegreeSL2006Calc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseHardegreeSL2006Proof
    , ndProcessLine = processLineHardegree
    , ndProcessLineMemo = Nothing
    , ndNotation  = hardegreeNotation
    , ndParseSeq = parseSeqOver (purePropFormulaParser hardegreeOpts)
    , ndParseForm = purePropFormulaParser hardegreeOpts
    }
