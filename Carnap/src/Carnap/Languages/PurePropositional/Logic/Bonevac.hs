{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Bonevac
    (parseBonevacSL,  parseBonevacSLProof, BonevacSL(..), bonevacSLCalc) where

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
import Carnap.Languages.PurePropositional.Logic.Rules

--A system for propositional logic resembling the proof system fron Daniel
--Bonevac's Deduction

data BonevacSL = As | AndE1 | AndE2 | AndI 
               | NegE | NegI  
               | ID1 | ID2 | ID3 | ID4 | ID5 | ID6 | ID7 | ID8 
               | IfE1 | IfE2  | IfI1 | IfI2
               | IffI | CB1 | CB2 | IffE1 | IffE2 | IffE3 | IffE4
               | OrI1 | OrI2 | OrE1 | OrE2 | OrE3
               | NegAndI | NegAndE
               | NegOrI  | NegOrE
               | NegIfI  | NegIfE
               | NegIffI1 | NegIffI2 | NegIffE1 | NegIffE2
               | CondDisj1 | CondDisj2
               | CommAnd | AssAnd1 | AssAnd2
               | CommOr  | AssOr1  | AssOr2
               | EFQ | AIP | ACP | R | DP
               deriving (Eq)

instance Show BonevacSL where
    show As        = "A"
    show AndE1     = "&E"
    show AndE2     = "&E"
    show AndI      = "&I"
    show NegE      = "DN"
    show NegI      = "DN"
    show ID1        = ""
    show ID2        = ""
    show ID3        = ""
    show ID4        = ""
    show ID5        = ""
    show ID6        = ""
    show ID7        = ""
    show ID8        = ""
    show IfE1      = "→E"
    show IfE2      = "→E*"
    show IfI1       = ""
    show IfI2       = ""
    show IffI      = "↔I"
    show CB1       = "→↔"
    show CB2       = "→↔"
    show IffE1     = "↔E"
    show IffE2     = "↔E"
    show IffE3     = "↔E*"
    show IffE4     = "↔E*"
    show OrI1      = "∨I"
    show OrI2      = "∨I"
    show OrE1      = "∨E"
    show OrE2      = "∨E*"
    show OrE3      = "∨E*"
    show NegAndI   = "¬&"
    show NegAndE   = "¬&"
    show NegOrI    = "¬∨"
    show NegOrE    = "¬∨"
    show NegIfI    = "¬→"
    show NegIfE    = "¬→"
    show NegIffI1  = "¬↔"
    show NegIffI2  = "¬↔"
    show NegIffE1  = "¬↔"
    show NegIffE2  = "¬↔"
    show CondDisj1 = "→∨"
    show CondDisj2 = "→∨"
    show CommAnd   = "&C"
    show AssAnd1   = "&A"
    show AssAnd2   = "&A"
    show CommOr    = "∨C"
    show AssOr1    = "∨A"
    show AssOr2    = "∨A"
    show EFQ       = "!"
    show AIP       = "AIP"
    show ACP       = "ACP"
    show R         = "R"
    show DP        = ""

instance Inference BonevacSL PurePropLexicon (Form Bool) where
          ruleOf As        = axiom
          ruleOf AndE1     = simplificationVariations !! 0
          ruleOf AndE2     = simplificationVariations !! 1
          ruleOf AndI      = adjunction
          ruleOf NegE      = doubleNegation !! 0
          ruleOf NegI      = doubleNegation !! 1
          ruleOf ID1       = constructiveReductioVariations !! 0
          ruleOf ID2       = constructiveReductioVariations !! 1
          ruleOf ID3       = constructiveReductioVariations !! 2
          ruleOf ID4       = constructiveReductioVariations !! 3
          ruleOf ID5       = nonConstructiveReductioVariations !! 0
          ruleOf ID6       = nonConstructiveReductioVariations !! 1
          ruleOf ID7       = nonConstructiveReductioVariations !! 2
          ruleOf ID8       = nonConstructiveReductioVariations !! 3
          ruleOf IfE1      = modusPonens
          ruleOf IfE2      = modusTollens
          ruleOf IfI1      = explicitConditionalProofVariations !! 0
          ruleOf IfI2      = explicitConditionalProofVariations !! 1
          ruleOf IffI      = conditionalToBiconditional
          ruleOf CB1       = biconditionalToConditionalVariations !! 0
          ruleOf CB2       = biconditionalToConditionalVariations !! 1
          ruleOf IffE1     = biconditionalPonensVariations !! 0
          ruleOf IffE2     = biconditionalPonensVariations !! 1
          ruleOf IffE3     = biconditionalTollensVariations !! 0
          ruleOf IffE4     = biconditionalTollensVariations !! 1
          ruleOf OrI1      = additionVariations !! 0
          ruleOf OrI2      = additionVariations !! 1
          ruleOf OrE1      = dilemma
          ruleOf OrE2      = modusTollendoPonensVariations !! 0 
          ruleOf OrE3      = modusTollendoPonensVariations !! 1
          ruleOf NegAndI   = deMorgansLaws !! 0
          ruleOf NegAndE   = deMorgansLaws !! 1
          ruleOf NegOrI    = deMorgansLaws !! 2
          ruleOf NegOrE    = deMorgansLaws !! 3
          ruleOf NegIfI    = negatedConditional !! 0
          ruleOf NegIfE    = negatedConditional !! 1
          ruleOf NegIffI1  = negatedBiconditional !! 0
          ruleOf NegIffE1  = negatedBiconditional !! 1
          ruleOf NegIffI2  = negatedBiconditional !! 2
          ruleOf NegIffE2  = negatedBiconditional !! 3
          ruleOf CondDisj1 = materialConditional !! 0
          ruleOf CondDisj2 = materialConditional !! 1
          ruleOf CommAnd   = andCommutativity !! 0
          ruleOf AssAnd1   = andAssociativity !! 0
          ruleOf AssAnd2   = andAssociativity !! 1 
          ruleOf CommOr    = orCommutativity !! 0
          ruleOf AssOr1    = orAssociativity !! 0
          ruleOf AssOr2    = orAssociativity !! 1
          ruleOf EFQ       = exfalso
          ruleOf AIP       = axiom
          ruleOf ACP       = axiom
          ruleOf R         = identityRule
          ruleOf DP        = identityRule

          indirectInference  AIP = Just (DeferredTo (TypedProof (ProofType 0 2)))
          indirectInference  ACP = Just (DeferredTo (TypedProof (ProofType 1 1)))
          indirectInference x 
             | x `elem` [DP,ID1,ID2,ID3,ID4,ID5,ID6,ID7,ID8,IfI1,IfI2] = Just (DeferTo 1)
             | otherwise = Nothing

          globalRestriction (Left ded) n As = Just $ \_ -> if all (== Just [As]) . map ruleOfLine . take n $ ded 
                                                             then Nothing
                                                             else Just "assumptions can occur only at the top of the proof"
          globalRestriction _ _ _ = Nothing

          isAssumption As = True
          isAssumption AIP = True
          isAssumption ACP = True
          isAssumption _ = False

          restriction _ = Nothing

parseBonevacSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [BonevacSL]
parseBonevacSL rtc = do ms <- optionMaybe (spaces >> eof)
                        case ms of 
                           Just _ -> return [DP, ID1,ID2,ID3,ID4,ID5,ID6,ID7,ID8,IfI1,IfI2]
                           Nothing -> do
                                r <- choice (map (try . string) ["AIP" ,"ACP" , "A","&I","/\\I", "^I","&E","/\\E", "^E"
                                                                ,"~~","--","¬¬","DN","R" , "->E*", "→E*", "MT","->E", "→E"
                                                                , "MP", "<->I","↔I" , "-><->", "→↔","<->E*", "↔E*","<->E", "↔E"
                                                                , "vI", "\\/I", "vE*", "\\/E*" , "∨E*", "DS", "∨I","vE", "\\/E"
                                                                , "∨E", "CD","!","~&", "-&", "~/\\","-/\\","~^", "-&", "¬∧", "¬&"
                                                                , "~v", "-v", "~\\/", "-\\/", "¬∨","~->", "-->", "¬→","~<->", "-<->"
                                                                , "¬↔","->v", "->\\/", "→∨","&C","/\\C", "^C", "∧C"
                                                                , "&A","/\\A", "^A", "∧A","vC","\\/C", "∨C","vA","\\/A", "∨A"])
                                return $ case r of
                                     r | r == "A" -> [As]
                                       | r `elem` ["&I","/\\I", "^I"] -> [AndI]
                                       | r `elem` ["&E","/\\E", "^E"] -> [AndE1, AndE2]
                                       | r `elem` ["~~","--","¬¬","DN"] -> [NegE, NegI]
                                       | r `elem` ["R"] -> [R]
                                       | r `elem` ["->E", "→E", "MP"] -> [IfE1]
                                       | r `elem` ["->E*", "→E*", "MT"] -> [IfE2]
                                       | r `elem` ["<->I","↔I"] -> [IffI]
                                       | r `elem` ["AIP"] -> [AIP]
                                       | r `elem` ["ACP"] -> [ACP]
                                       | r `elem` ["-><->", "→↔"] -> [CB1,CB2]
                                       | r `elem` ["<->E", "↔E"] -> [IffE1, IffE2]
                                       | r `elem` ["<->E*", "↔E*"] -> [IffE3, IffE4]
                                       | r `elem` ["vI", "\\/I", "∨I"] -> [OrI1, OrI2]
                                       | r `elem` ["vE", "\\/E", "∨E", "CD"] -> [OrE1]
                                       | r `elem` ["vE*", "\\/E*", "∨E*", "DS"] -> [OrE2, OrE3]
                                       | r `elem` ["!"] -> [EFQ]
                                       | r `elem` ["~&", "-&", "~/\\","-/\\","~^", "-&", "¬∧", "¬&"] -> [NegAndI, NegAndE]
                                       | r `elem` ["~v", "-v", "~\\/", "-\\/", "¬∨"] -> [NegOrI, NegOrE]
                                       | r `elem` ["~->", "-->", "¬→"] -> [NegIfI, NegIfE]
                                       | r `elem` ["~<->", "-<->", "¬↔"] -> [NegIffI1,NegIffI2, NegIffE1, NegIffE2]
                                       | r `elem` ["->v", "->\\/", "→∨"] -> [CondDisj1, CondDisj2]
                                       | r `elem` ["&C","/\\C", "^C", "∧C"] -> [CommAnd]
                                       | r `elem` ["&A","/\\A", "^A", "∧A"] -> [AssAnd1,AssAnd2]
                                       | r `elem` ["vC","\\/C", "∨C"] -> [CommOr]
                                       | r `elem` ["vA","\\/A", "∨A"] -> [AssOr1,AssOr2]

parseBonevacSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine BonevacSL PurePropLexicon (Form Bool)]
parseBonevacSLProof rtc = toDeductionHardegree (parseBonevacSL rtc) (purePropFormulaParser bonevacOpts)

bonevacNotation :: String -> String
bonevacNotation (x:xs) | isUpper x = toLower x : bonevacNotation xs
                       | otherwise = x : bonevacNotation xs
bonevacNotation [] = []

bonevacSLCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseBonevacSLProof
    , ndProcessLine = processLineHardegree
    , ndProcessLineMemo = Just hoProcessLineHardegreeMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser bonevacOpts)
    , ndParseForm = purePropFormulaParser bonevacOpts
    , ndNotation = bonevacNotation
    }
