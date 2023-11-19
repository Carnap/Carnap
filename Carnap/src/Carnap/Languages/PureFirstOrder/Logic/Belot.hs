{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Belot
    ( belotPDCalc, parseBelotPD
    , belotPDPlusCalc, parseBelotPDPlus
    , belotPDECalc,parseBelotPDE
    , belotPDEPlusCalc, parseBelotPDEPlus
    , BelotPD(..), BelotPDPlus(..)
    , BelotPDE(..), BelotPDEPlus(..)) where

import Data.Map as M (lookup, Map,empty)
import Data.Char (toLower)
import Data.List (intercalate)
import Text.Parsec
import Carnap.Core.Data.Types (Form, Term)
import Carnap.Core.Unification.Unification
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Belot hiding (SD,Pr)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PureFirstOrder.Util
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint, fitchAssumptionCheck, axiom)

data BelotPD = SD BelotSD | UI | UE 
                 | EI | EE1 | EE2 
                 | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
                 deriving Eq

instance Show BelotPD where
        show (SD x) = show x
        show UI          = "(∀I)"
        show UE          = "(∀E)"
        show EI          = "(∃I)"
        show EE1         = "(∃E)"
        show EE2         = "(∃E)"
        show (Pr _)      = "A"

instance Inference BelotPD PureLexiconFOL (Form Bool) where

         ruleOf UI   = universalGeneralization
         ruleOf UE   = universalInstantiation
         ruleOf EI   = existentialGeneralization
         ruleOf EE1  = existentialDerivation !! 0 
         ruleOf EE2  = existentialDerivation !! 1 
         ruleOf (Pr _) = axiom
         ruleOf x@(SD _) = SequentRule (premisesOf x) (conclusionOf x)

         premisesOf (SD x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (SD x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (SD x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI  = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
         restriction EE1 = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2 = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _ = Nothing

         isAssumption (SD x) = isAssumption x
         isAssumption _ = False

         isPremise (Pr _) = True
         isPremise _ = False

         globalRestriction (Left ded) n (SD CondIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (SD CondIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (SD NegeIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD NegeIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD NegeIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD NegeIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD NegeElim1) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD NegeElim2) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD NegeElim3) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD NegeElim4) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (SD DisjElim1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SD DisjElim2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SD DisjElim3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SD DisjElim4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (SD BicoIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (SD BicoIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (SD BicoIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (SD BicoIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction _ _ _ = Nothing

parseBelotPD rtc = try quantRule <|> liftProp 
    where liftProp = do r <- parseBelotSD (defaultRuntimeDeductionConfig)
                        return (map SD r)
          quantRule = do r <- (char '(' *> choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE"]) <* char ')')
                              <|> try ((++) <$> string "A/" <*> many (noneOf ")"))
                              <|> choice (map (try . string) ["PR", "A"])
                         return $ case r of 
                            r | r `elem` ["∀I","AI"] -> [UI]
                              | r `elem` ["∀E","AE"] -> [UE]
                              | r `elem` ["∃I","EI"] -> [EI]
                              | r `elem` ["∃E","EE"] -> [EE1, EE2]
                              | r `elem` [ "A", "PR", "Assumption"] -> [Pr (problemPremises rtc)]
                              | r `elem` ["A/EE"] -> [SD $ AS "/∃E"]
                              | r `elem` ["A/>I", "A/->I"] -> [SD $ AS "/⊃I"]
                              | r `elem` ["A/=I"] -> [SD $ AS "/≡I"]
                            'A':'/':rest -> [SD $ AS (" / " ++ rest)]

parseBelotPDProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine BelotPD PureLexiconFOL (Form Bool)]
parseBelotPDProof rtc = toDeductionFitch (parseBelotPD rtc) belotPDFormulaParser --XXX Check parser

belotNotation :: String -> String 
belotNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleCon <|> try handleQuant <|> try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleCon = (char '∧' >> return "&") 
                      <|> (char '¬' >> return "~") 
                      <|> (char '→' >> return "⊃")
                      <|> (char '↔' >> return "≡")
                      <|> (char '⊤' >> return " ")
          handleQuant = do q <- oneOf "∀∃"
                           v <- anyChar
                           return $ "(" ++ [q] ++ [v] ++ ")"
          handleAtom = try handlePred <|> handleSent
          handlePred = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- handleTerm `sepBy` char ','
                          char ')'
                          return $ c : concat args
          handleSent = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                          return $ [toLower c]
          handleTerm = try handleFunc <|> handleConst
          handleFunc = do c <- oneOf "abcdefghijklmnopqrstuvwxyz" <* char '('
                          args <- handleTerm `sepBy` char ','
                          char ')'
                          return $ [c,'('] ++ intercalate "," args ++ ")"
          handleConst = do c <- oneOf "abcdefghijklmnopqrstuvwxyz" 
                           return [c]
          fallback = do c <- anyChar 
                        return [c]

belotPDCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseBelotPDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver belotPDFormulaParser
    , ndParseForm = belotPDFormulaParser
    , ndNotation = belotNotation
    }

data BelotPDPlus = PDtoPDP BelotPD | SDPlus BelotSDPlus | QN1 | QN2 | QN3 | QN4

instance Show BelotPDPlus where
        show (SDPlus x) = show x
        show (PDtoPDP x) = show x
        show QN1 = "(QN)"
        show QN2 = "(QN)"
        show QN3 = "(QN)"
        show QN4 = "(QN)"

instance Inference BelotPDPlus PureLexiconFOL (Form Bool) where

         ruleOf QN1 = quantifierNegationReplace !! 0
         ruleOf QN2 = quantifierNegationReplace !! 1
         ruleOf QN3 = quantifierNegationReplace !! 2
         ruleOf QN4 = quantifierNegationReplace !! 3
         ruleOf (SDPlus Com1) = andCommutativity !! 0
         ruleOf (SDPlus Com2) = orCommutativity !! 0
         ruleOf (SDPlus Assoc1) = andAssociativity !! 0
         ruleOf (SDPlus Assoc2) = andAssociativity !! 1 
         ruleOf (SDPlus Assoc3) = orAssociativity !! 0  
         ruleOf (SDPlus Assoc4) = orAssociativity !! 1  
         ruleOf (SDPlus Impl1) = materialConditional !! 0
         ruleOf (SDPlus Impl2) = materialConditional !! 1
         ruleOf (SDPlus DN1) = doubleNegation !! 0
         ruleOf (SDPlus DN2) = doubleNegation !! 1
         ruleOf (SDPlus DeM1) = deMorgansLaws !! 0 
         ruleOf (SDPlus DeM2) = deMorgansLaws !! 1
         ruleOf (SDPlus DeM3) = deMorgansLaws !! 2
         ruleOf (SDPlus DeM4) = deMorgansLaws !! 3
         ruleOf (SDPlus Idem1) = andIdempotence !! 0
         ruleOf (SDPlus Idem2) = andIdempotence !! 1
         ruleOf (SDPlus Idem3) = orIdempotence !! 0
         ruleOf (SDPlus Idem4) = orIdempotence !! 1
         ruleOf (SDPlus Trans1) = contraposition !! 0
         ruleOf (SDPlus Trans2) = contraposition !! 1
         ruleOf (SDPlus Exp1) = exportation !! 0
         ruleOf (SDPlus Exp2) = exportation !! 1
         ruleOf (SDPlus Dist1) = distribution !! 0
         ruleOf (SDPlus Dist2) = distribution !! 1
         ruleOf (SDPlus Dist3) = distribution !! 4
         ruleOf (SDPlus Dist4) = distribution !! 5
         ruleOf (SDPlus Equiv1) = biconditionalExchange !! 0
         ruleOf (SDPlus Equiv2) = biconditionalExchange !! 1
         ruleOf (SDPlus Equiv3) = biconditionalCases !! 0
         ruleOf (SDPlus Equiv4) = biconditionalCases !! 1
         ruleOf (PDtoPDP x) = ruleOf x
         ruleOf r@(SDPlus x) = premisesOf r ∴ conclusionOf r

         premisesOf r@(SDPlus x) | x `elem` replacements = upperSequents (ruleOf r)
            where replacements = [Com1, Com2, Com3, Com4 , Assoc1, Assoc2, Assoc3, Assoc4 
                                 , Impl1, Impl2 , DN1 , DN2 , DeM1, DeM2, DeM3, DeM4 
                                 , Idem1, Idem2, Idem3, Idem4 , Trans1, Trans2 
                                 , Exp1, Exp2 , Dist1, Dist2, Dist3, Dist4 
                                 , Equiv1, Equiv2, Equiv3, Equiv4]
         premisesOf (SDPlus x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf r@(SDPlus x) | x `elem` replacements = lowerSequent (ruleOf r)
            where replacements = [Com1, Com2, Com3, Com4 , Assoc1, Assoc2, Assoc3, Assoc4 
                                 , Impl1, Impl2 , DN1 , DN2 , DeM1, DeM2, DeM3, DeM4 
                                 , Idem1, Idem2, Idem3, Idem4 , Trans1, Trans2 
                                 , Exp1, Exp2 , Dist1, Dist2, Dist3, Dist4 
                                 , Equiv1, Equiv2, Equiv3, Equiv4]
         conclusionOf (SDPlus x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (SDPlus x) = indirectInference x
         indirectInference (PDtoPDP x) = indirectInference x
         indirectInference _ = Nothing 

         restriction (PDtoPDP x) = restriction x
         restriction _ = Nothing

         isAssumption (SDPlus x) = isAssumption x
         isAssumption (PDtoPDP x) = isAssumption x
         isAssumption _ = False

         isPremise (PDtoPDP x) = isPremise x
         isPremise _ = False

         globalRestriction (Left ded) n (PDtoPDP (SD CondIntro1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD CondIntro2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeIntro1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeIntro2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeIntro3)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeIntro4)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeElim1)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeElim2)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeElim3)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD NegeElim4)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDP (SD DisjElim1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDP (SD DisjElim2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDP (SD DisjElim3)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDP (SD DisjElim4)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDP (SD BicoIntro1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDtoPDP (SD BicoIntro2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDtoPDP (SD BicoIntro3)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDtoPDP (SD BicoIntro4)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction _ _ _ = Nothing

parseBelotPDPlus rtc = try liftPD <|> try liftProp <|> qn
    where liftPD = map PDtoPDP <$> parseBelotPD rtc
          liftProp =  map SDPlus <$> parseBelotSDPlus (defaultRuntimeDeductionConfig)
          qn = string "(QN)" >> return [QN1, QN2, QN3, QN4]

parseBelotPDPlusProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine BelotPDPlus PureLexiconFOL (Form Bool)]
parseBelotPDPlusProof rtc = toDeductionFitch (parseBelotPDPlus rtc) belotPDFormulaParser --XXX Check parser

belotPDPlusCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseBelotPDPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver belotPDFormulaParser
    , ndParseForm = belotPDFormulaParser
    , ndNotation = belotNotation
    }

data BelotPDE = PDtoPDE BelotPD | II | IE1 | IE2
                  deriving Eq

instance Show BelotPDE where
        show (PDtoPDE x) = show x
        show II  = "(=I)"
        show IE1 = "(=E)"
        show IE2 = "(=E)"

instance Inference BelotPDE PureLexiconFOL (Form Bool) where
         ruleOf II = [] ∴ Top :|-: SS (lall "v" equality)
            where equality :: ClassicalSequentOver PureLexiconFOL (Term Int) -> ClassicalSequentOver PureLexiconFOL (Form Bool)
                  equality x = x `equals` x
         ruleOf IE1 = leibnizLawVariations !! 0
         ruleOf IE2 = leibnizLawVariations !! 1
         ruleOf (PDtoPDE x) = ruleOf x

         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (PDtoPDE x) = indirectInference x
         indirectInference _ = Nothing 

         restriction (PDtoPDE UE) = Just (closedTerm [tau])
         restriction (PDtoPDE EI) = Just (closedTerm [tau])
         restriction (PDtoPDE x) = restriction x
         restriction IE1 = Just (closedTerm [tau, tau'])
         restriction IE2 = Just (closedTerm [tau, tau'])
         restriction _ = Nothing

         isAssumption (PDtoPDE x) = isAssumption x
         isAssumption _ = False

         isPremise (PDtoPDE x) = isPremise x
         isPremise _ = False

         globalRestriction (Left ded) n (PDtoPDE (SD CondIntro1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD CondIntro2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeIntro1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeIntro2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeIntro3)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeIntro4)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeElim1)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeElim2)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeElim3)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD NegeElim4)) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDtoPDE (SD DisjElim1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDE (SD DisjElim2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDE (SD DisjElim3)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDE (SD DisjElim4)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDtoPDE (SD BicoIntro1)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDtoPDE (SD BicoIntro2)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDtoPDE (SD BicoIntro3)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDtoPDE (SD BicoIntro4)) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction _ _ _ = Nothing

closedTerm :: [ClassicalSequentOver PureLexiconFOL (Term Int)] -> [Equation (ClassicalSequentOver PureLexiconFOL)] -> Maybe String
closedTerm [] sub = Nothing
closedTerm (x:xs) sub 
    | isOpenTerm (applySub sub x) = Just $ "the term " ++ show (applySub sub x) ++ " appears not to be closed."
    | otherwise = closedTerm xs sub

parseBelotPDE rtc = try liftPD <|> parseEq
    where liftPD = map PDtoPDE <$> parseBelotPD rtc
          parseEq = try (string "(=E)" >> return [IE1,IE2]) <|> (string "(=I)" >> return [II])

parseBelotPDEProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine BelotPDE PureLexiconFOL (Form Bool)]
parseBelotPDEProof rtc = toDeductionFitch (parseBelotPDE rtc) belotPDEFormulaParser

belotPDECalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseBelotPDEProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver belotPDEFormulaParser
    , ndParseForm = belotPDEFormulaParser
    , ndNotation = belotNotation
    }

data BelotPDEPlus = PDPtoPDEP BelotPDPlus | PDEtoPDEP BelotPDE

instance Show BelotPDEPlus where
        show (PDPtoPDEP x) = show x
        show (PDEtoPDEP x) = show x

instance Inference BelotPDEPlus PureLexiconFOL (Form Bool) where
         ruleOf (PDPtoPDEP x) = ruleOf x
         ruleOf (PDEtoPDEP x) = ruleOf x

         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (PDPtoPDEP x) = indirectInference x
         indirectInference (PDEtoPDEP x) = indirectInference x
         indirectInference _ = Nothing 

         restriction (PDEtoPDEP x) = restriction x
         restriction (PDPtoPDEP x) = restriction x
         restriction _ = Nothing

         isAssumption (PDEtoPDEP x) = isAssumption x
         isAssumption (PDPtoPDEP x) = isAssumption x
         isAssumption _ = False

         isPremise (PDEtoPDEP x) = isPremise x
         isPremise (PDPtoPDEP x) = isPremise x
         isPremise _ = False

         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD CondIntro1))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD CondIntro2))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeIntro1))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeIntro2))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeIntro3))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeIntro4))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeElim1))) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeElim2))) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeElim3))) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD NegeElim4))) = Just $
            fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD DisjElim1))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD DisjElim2))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD DisjElim3))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD DisjElim4))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD BicoIntro1))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD BicoIntro2))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD BicoIntro3))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (PDEtoPDEP (PDtoPDE (SD BicoIntro4))) = Just $
            fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction _ _ _ = Nothing

parseBelotPDEPlus rtc = try liftPDE <|> liftPDP
    where liftPDP = map PDPtoPDEP <$> parseBelotPDPlus rtc
          liftPDE = map PDEtoPDEP <$> parseBelotPDE rtc

parseBelotPDEPlusProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine BelotPDEPlus PureLexiconFOL (Form Bool)]
parseBelotPDEPlusProof rtc = toDeductionFitch (parseBelotPDEPlus rtc) belotPDEFormulaParser

belotPDEPlusCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseBelotPDEPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver belotPDEFormulaParser
    , ndParseForm = belotPDEFormulaParser
    , ndNotation = belotNotation
    }
