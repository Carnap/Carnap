{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Hurley
    (parseHurleySL,  parseHurleySLProof, HurleySL(..), hurleySLCalc) where

import Data.Map as M (lookup, Map)
import Data.Char
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PurePropositional.Logic.Rules

--A system for propositional logic resembling the proof system fron
--Hurley's "Concise Introduction to Logic"

data HurleySL  = MP | MT | DS1 | DS2 | HS | CD 
               | Simp | Conj | Add
               --the rest are rules of replacement
               | DM1 | DM2 | DM3  | DM4
               | ComOr | ComAnd
               | AssocOr1 | AssocOr2 | AssocAnd1 | AssocAnd2
               | DistAnd1 | DistAnd2 | DistOr1 | DistOr2
               | DN1 | DN2
               | Trans1 | Trans2
               | Exp1 | Exp2
               | Impl1 | Impl2
               | Taut1 | Taut2 | Taut3 | Taut4
               | Equiv1  | Equiv2 | Equiv3 | Equiv4
               | CP1 | CP2 | ACP
               | IP1 | IP2 | AIP
               | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
               deriving (Eq)

instance Show HurleySL where
        show MP = "MP"
        show MT = "MT"
        show DS1 = "DS"
        show DS2 = "DS"
        show HS = "HS"
        show CD = "CD"
        show Simp = "Simp"
        show Conj = "Conj"
        show Add = "Add"
        show DM1 = "DM"
        show DM2 = "DM"
        show DM3 = "DM"
        show DM4 = "DM"
        show ComOr = "Com"
        show ComAnd = "Com"
        show AssocOr1 = "Assoc"
        show AssocOr2 = "Assoc"
        show AssocAnd1 = "Assoc"
        show AssocAnd2 = "Assoc"
        show DistAnd1 = "Dist"
        show DistAnd2 = "Dist"
        show DistOr1 = "Dist"
        show DistOr2 = "Dist"
        show DN1 = "DN"
        show DN2 = "DN"
        show Trans1 = "Trans"
        show Trans2 = "Trans"
        show Exp1 = "Exp"
        show Exp2 = "Exp"
        show Impl1 = "Impl"
        show Impl2 = "Impl"
        show Taut1 = "Taut"
        show Taut2 = "Taut"
        show Taut3 = "Taut"
        show Taut4 = "Taut"
        show Equiv1 = "Equiv"
        show Equiv2 = "Equiv" 
        show Equiv3 = "Equiv"
        show Equiv4 = "Equiv" 
        show CP1 = "CP" 
        show CP2 = "CP" 
        show ACP = "ACP" 
        show IP1 = "IP" 
        show IP2 = "IP"
        show AIP = "AIP"
        show (Pr _) = ""

instance Inference HurleySL PurePropLexicon (Form Bool) where
        ruleOf MP = modusPonens
        ruleOf MT = modusTollens
        ruleOf DS1 = modusTollendoPonensVariations !! 0
        ruleOf DS2 = modusTollendoPonensVariations !! 1
        ruleOf HS = hypotheticalSyllogism
        ruleOf CD = conjunctionDilemma
        ruleOf Simp = simplificationVariations !! 0
        ruleOf Conj = adjunction
        ruleOf Add = additionVariations !! 1
        ruleOf DM1 = deMorgansLaws !! 0
        ruleOf DM2 = deMorgansLaws !! 1
        ruleOf DM3 = deMorgansLaws !! 2
        ruleOf DM4 = deMorgansLaws !! 3
        ruleOf ComOr = orCommutativity !! 0
        ruleOf ComAnd = andCommutativity !! 0
        ruleOf AssocOr1 = orAssociativity !! 0
        ruleOf AssocOr2 = orAssociativity !! 1
        ruleOf AssocAnd1 = andAssociativity !! 0
        ruleOf AssocAnd2 = andAssociativity !! 1
        ruleOf DistAnd1 = andDistributivity !! 0
        ruleOf DistAnd2 = andDistributivity !! 1
        ruleOf DistOr1 = orDistributivity !! 0
        ruleOf DistOr2 = orDistributivity !! 1
        ruleOf DN1 = doubleNegation !! 0
        ruleOf DN2 = doubleNegation !! 1
        ruleOf Trans1 = contraposition !! 0
        ruleOf Trans2 = contraposition !! 1
        ruleOf Exp1 = exportation !! 0
        ruleOf Exp2 = exportation !! 1
        ruleOf Impl1 = materialConditional !! 0
        ruleOf Impl2 = materialConditional !! 1
        ruleOf Taut1 = andIdempotence !! 0
        ruleOf Taut2 = andIdempotence !! 1
        ruleOf Taut3 = orIdempotence !! 0
        ruleOf Taut4 = orIdempotence !! 1
        ruleOf Equiv1 = biconditionalExchange !! 0
        ruleOf Equiv2 = biconditionalExchange !! 1 
        ruleOf Equiv3 = biconditionalCases !! 0
        ruleOf Equiv4 = biconditionalCases !! 1
        ruleOf CP1 = conditionalProofVariations !! 0
        ruleOf CP2 = conditionalProofVariations !! 1 
        ruleOf ACP = axiom
        ruleOf IP1 = constructiveConjunctionReductioVariations !! 0
        ruleOf IP2 = constructiveConjunctionReductioVariations !! 1
        ruleOf AIP = axiom
        ruleOf (Pr _) = axiom

        indirectInference x
            | x `elem` [CP1,CP2,IP1,IP2] = Just PolyProof
            | otherwise = Nothing

        isAssumption AIP = True
        isAssumption ACP = True
        isAssumption _ = False

        isPremise (Pr _) = True
        isPremise _ = False

        globalRestriction (Left ded) n CP1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n CP2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n IP1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2 .∧. (lneg $ phin 2)])]
        globalRestriction (Left ded) n IP2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2 .∧. (lneg $ phin 2)])]
        globalRestriction _ _ _ = Nothing

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

parseHurleySL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [HurleySL]
parseHurleySL rtc = do ms <- optionMaybe ((spaces >> eof >> return ()) <|>  (string "/" >> many anyChar >> return ()))
                       case ms of 
                            Just _ -> return [Pr (problemPremises rtc)]
                            Nothing -> do
                                    r <- choice (map (try . string) ["MP", "MT", "DS", "HS", "CD", "Simp", "Conj", "Add"
                                                                    , "DM", "Com", "Assoc", "Dist", "DN", "Trans", "Exp"
                                                                    , "Impl", "Taut", "Equiv", "CP" ,"ACP" ,"IP" ,"AIP"])
                                    return $ case r of 
                                         "MP" -> [MP]
                                         "MT" -> [MT]
                                         "DS" -> [DS1,DS2]
                                         "HS" -> [HS]
                                         "CD" -> [CD]
                                         "Simp" -> [Simp]
                                         "Conj" -> [Conj]
                                         "Add" -> [Add]
                                         "DM" -> [DM1,DM2,DM3,DM4]
                                         "Com" -> [ComOr,ComAnd]
                                         "Assoc" -> [AssocOr1,AssocOr2,AssocAnd1,AssocAnd2]
                                         "Dist" -> [DistAnd1,DistAnd2,DistOr1,DistOr2]
                                         "DN" -> [DN1,DN2]
                                         "Trans" -> [Trans1,Trans2]
                                         "Exp" -> [Exp1,Exp2]
                                         "Impl" -> [Impl1,Impl2]
                                         "Taut" -> [Taut1,Taut2,Taut3,Taut4]
                                         "Equiv" -> [Equiv1,Equiv2,Equiv3,Equiv4]
                                         "CP"  -> [CP1,CP2]
                                         "ACP"  -> [ACP]
                                         "IP"  -> [IP1,IP2]
                                         "AIP" -> [AIP]

parseHurleySLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine HurleySL PurePropLexicon (Form Bool)]
parseHurleySLProof rtc = toDeductionFitchAlt (parseHurleySL rtc) (purePropFormulaParser hurleyOpts)

--XXX: similar to hausman, but with ≡ for iff
hurleySLNotation :: String -> String 
hurleySLNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- handleCon <|> try handleQuant <|> try handleAtom <|> handleLParen <|> handleRParen <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleCon = (char '∧' >> return "∙") <|> (char '¬' >> return "~") <|> (char '→' >> return "⊃") <|> (char '↔' >> return "≡")
          handleQuant = do q <- oneOf "∀∃"
                           v <- anyChar
                           return $ "(" ++ (if q == '∃' then "∃" else "") ++ [v] ++ ")"
          handleLParen = do char '('
                            n <- getState 
                            putState (n + 1)
                            return $ ["(","[","{"] !! (n `mod` 3) 
          handleRParen = do char ')'
                            n <- getState 
                            putState (n - 1)
                            return $ [")","]","}"] !! ((n - 1) `mod` 3)
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          fallback = do c <- anyChar 
                        return [c]

hurleySLCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseHurleySLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser hurleyOpts)
    , ndParseForm = purePropFormulaParser hurleyOpts
    , ndNotation = hurleySLNotation
    }
