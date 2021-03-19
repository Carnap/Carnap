{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gamut 
    ( GamutMPND(..), gamutMPNDCalc, parseGamutMPND
    , GamutIPND(..), gamutIPNDCalc, parseGamutIPND
    , GamutPND(..), gamutPNDCalc, parseGamutPND
    , GamutPNDPlus(..), gamutPNDPlusCalc, parseGamutPNDPlus
    ) where

import Text.Parsec
import Data.Char
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,subst,FirstOrder)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser (parseSeqOver)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules

data GamutMPND = InAnd  | ElimAndL | ElimAndR
               | ElimIf | InIf1    | InIf2
               | InNeg1 | InNeg2   | ElimNeg 
               | ElimOr | InOrL    | InOrR 
               | AS     | PR       | Rep
    deriving Eq

data GamutIPND = MPND GamutMPND | EFSQ
    deriving Eq

data GamutPND = IPND GamutIPND | DNE
    deriving Eq

data GamutPNDPlus = PND GamutPND 
                  | LEM | LNC | DN1 | DN2
                  | LCC  | LCD  | LAC1 | LAC2 | LAD1 | LAD2
                  | LDD1 | LDD2 | LDC1 | LDC2 | DMOR1 | DMOR2
                  | DMAND1 | DMAND2 | MT | MTP | NMTP
    deriving Eq

instance Show GamutMPND where
        show InAnd      = "I∧"
        show ElimAndL   = "E∧"
        show ElimAndR   = "E∧"
        show ElimIf     = "E→"
        show InIf1      = "I→"
        show InIf2      = "I→"
        show InNeg1     = "I¬"
        show InNeg2     = "I¬"
        show ElimNeg    = "E¬"
        show ElimOr     = "E∨"
        show InOrL      = "I∨" 
        show InOrR      = "I∨"
        show AS         = "assumption"
        show PR         = "assumption"
        show Rep        = "repeat"

instance Show GamutIPND where
        show (MPND x)   = show x
        show EFSQ       = "EFSQ"

instance Show GamutPND where
        show (IPND x)   = show x
        show DNE        = "¬¬"

instance Show GamutPNDPlus where
        show (PND x)   = show x
        show LEM = "LEM"
        show LNC = "LNC"
        show DN1 = "DN"
        show DN2 = "DN"
        show LCC = "LCC"
        show LCD = "LCD" 
        show LAC1 = "LAC"
        show LAC2 = "LAC"
        show LAD1 = "LAD"
        show LAD2 = "LAD"
        show LDD1 = "LDD"
        show LDD2 = "LDD"
        show LDC1 = "LDC"
        show LDC2 = "LDC"
        show DMOR1 = "DMOR"
        show DMOR2 = "DMOR"
        show DMAND1 = "DMAND"
        show DMAND2 = "DMAND"
        show MT = "MT"
        show MTP = "PDS" 
        show NMTP = "NDS"

instance Inference GamutMPND PurePropLexicon (Form Bool) where
        ruleOf InAnd      = adjunction
        ruleOf ElimAndL   = simplificationVariations !! 0
        ruleOf ElimAndR   = simplificationVariations !! 1
        ruleOf ElimIf     = modusPonens
        ruleOf InIf1      = conditionalProofVariations !! 0
        ruleOf InIf2      = conditionalProofVariations !! 1
        ruleOf InNeg1     = constructiveFalsumReductioVariations !! 0
        ruleOf InNeg2     = constructiveFalsumReductioVariations !! 1
        ruleOf ElimNeg    = falsumIntroduction
        ruleOf ElimOr     = dilemma
        ruleOf Rep        = identityRule
        ruleOf InOrL      = additionVariations !! 0
        ruleOf InOrR      = additionVariations !! 1
        ruleOf AS         = axiom
        ruleOf PR         = axiom

        indirectInference x
            | x `elem` [InIf1, InIf2, InNeg1, InNeg2] = Just (WithAlternate (ImplicitProof (ProofType 0 1)) (TypedProof (ProofType 0 1)))
            | otherwise = Nothing

        isAssumption AS = True
        isAssumption _ = False

        globalRestriction (Left ded) n InIf1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n InIf2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n InNeg1 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n InNeg2 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

instance Inference GamutIPND PurePropLexicon (Form Bool) where
        ruleOf (MPND x) = ruleOf x
        ruleOf EFSQ     = falsumElimination

        indirectInference (MPND x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (MPND x) = isAssumption x
        isAssumption _ = False

        globalRestriction (Left ded) n (MPND InIf1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (MPND InIf2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (MPND InNeg1) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (MPND InNeg2) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

instance Inference GamutPND PurePropLexicon (Form Bool) where
        ruleOf (IPND x) = ruleOf x
        ruleOf DNE = doubleNegationElimination

        indirectInference (IPND x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (IPND x) = isAssumption x
        isAssumption _ = False

        globalRestriction (Left ded) n (IPND (MPND InIf1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (IPND (MPND InIf2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (IPND (MPND InNeg1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (IPND (MPND InNeg2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

instance Inference GamutPNDPlus PurePropLexicon (Form Bool) where
        ruleOf (PND x) = ruleOf x
        ruleOf LEM = [] ∴ Top :|-: SS (phin 1 .\/. (lneg $ phin 1))
        ruleOf LNC = [] ∴ Top :|-: SS (lneg (phin 1 ./\. (lneg $ phin 1)))
        ruleOf DN1 = doubleNegation !! 0
        ruleOf DN2 = doubleNegation !! 1
        ruleOf LCC = andCommutativity !! 0
        ruleOf LCD = orCommutativity !! 0
        ruleOf LAC1 = andAssociativity !! 0
        ruleOf LAC2 = andAssociativity !! 1
        ruleOf LAD1 = orAssociativity !! 0 
        ruleOf LAD2 = orAssociativity !! 1
        ruleOf LDD1 = orDistributivity !! 0
        ruleOf LDD2 = orDistributivity !! 1
        ruleOf LDC1 = andDistributivity !! 0
        ruleOf LDC2 = andDistributivity !! 1
        ruleOf DMOR1 = deMorgansLaws !! 0
        ruleOf DMOR2 = deMorgansLaws !! 1
        ruleOf DMAND1 = deMorgansLaws !! 2
        ruleOf DMAND2 = deMorgansLaws !! 3
        ruleOf MT = modusTollens
        ruleOf MTP = modusTollendoPonensVariations !! 0
        ruleOf NMTP = [ GammaV 1  :|-: SS (phin 1) 
                , GammaV 2  :|-: SS (lneg $ phin 1 .∧. phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 2)

        indirectInference (PND x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (PND x) = isAssumption x
        isAssumption _ = False

        globalRestriction (Left ded) n (PND (IPND (MPND InIf1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (PND (IPND (MPND InIf2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (PND (IPND (MPND InNeg1))) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (PND (IPND (MPND InNeg2))) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

parseGamutMPND rtc = do r <- choice (map (try . string) 
                                [ "I∧" , "I/\\", "I^", "E∧" , "E/\\", "E^"
                                , "E→" , "E->", "I→" , "I->"
                                , "I¬" , "I~", "I-", "E¬" , "E~", "E-"
                                , "E∨" , "E\\/", "Ev",  "I∨" , "I\\/", "Iv"
                                , "repetition", "rep" , "assumption", "as"])
                        case r of 
                         r | r `elem` ["I∧" , "I/\\", "I^"] -> return [InAnd]
                           | r `elem` ["E∧" , "E/\\", "E^"] -> return [ElimAndR, ElimAndL]
                           | r `elem` ["E→" , "E->"]        -> return [ElimIf]
                           | r `elem` ["I→" , "I->"]        -> return [InIf1, InIf2]
                           | r `elem` ["I¬" , "I~", "I-"]   -> return [InNeg1, InNeg2]
                           | r `elem` ["E¬" , "E~", "E-"]   -> return [ElimNeg]
                           | r `elem` ["E∨" , "E\\/", "Ev"] -> return [ElimOr]
                           | r `elem` ["I∨" , "I\\/", "Iv"] -> return [InOrL, InOrR]
                           | r `elem` ["repetition", "rep"] -> return [Rep]
                           | r `elem` ["assumption", "as"]  -> return [AS, PR]

parseGamutIPND rtc = (map MPND <$> parseGamutMPND rtc) <|> (try (string "EFSQ") >> return [EFSQ])

parseGamutPND rtc = (map IPND <$> parseGamutIPND rtc) 
                 <|> (choice (map (try . string) ["~~","¬¬","--"]) >> return [DNE])

parseGamutPNDPlus rtc = (map PND <$> parseGamutPND rtc) 
                 <|> parsePlus
    where parsePlus = do r <- choice (map (try . string) ["LEM", "LNC", "DN", "LCC", "LCD", "LAC", "LAD", "LDD", "LDC", "DMOR", "DMAND", "MT", "PDS", "NDS"])
                         return $ case r of
                           r | r == "LEM"   -> [LEM]
                             | r == "LNC"   -> [LNC]
                             | r == "DN"    -> [DN1, DN2]
                             | r == "LCC"   -> [LCC]
                             | r == "LCD"   -> [LCD]
                             | r == "LAC"   -> [LAC1,LAC2]
                             | r == "LAD"   -> [LAD1,LAD2]
                             | r == "LDD"   -> [LDD1,LDD2]
                             | r == "LDC"   -> [LDC1,LDC2]
                             | r == "DMOR"  -> [DMOR1,DMOR2]
                             | r == "DMAND" -> [DMAND1,DMAND2]
                             | r == "MT"    -> [MT]
                             | r == "PDS"   -> [MTP]
                             | r == "NDS"   -> [NMTP]

parseGamutMPNDProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutMPND PurePropLexicon (Form Bool)]
parseGamutMPNDProof rtc = toDeductionFitch (parseGamutMPND rtc) (purePropFormulaParser gamutOpts)

parseGamutIPNDProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutIPND PurePropLexicon (Form Bool)]
parseGamutIPNDProof rtc = toDeductionFitch (parseGamutIPND rtc) (purePropFormulaParser gamutOpts)

parseGamutPNDProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutPND PurePropLexicon (Form Bool)]
parseGamutPNDProof rtc = toDeductionFitch (parseGamutPND rtc) (purePropFormulaParser gamutOpts)

parseGamutPNDPlusProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine GamutPNDPlus PurePropLexicon (Form Bool)]
parseGamutPNDPlusProof rtc = toDeductionFitch (parseGamutPNDPlus rtc) (purePropFormulaParser gamutOpts)

gamutNotation :: String -> String
gamutNotation (x:xs) | isUpper x = toLower x : gamutNotation xs
                     | otherwise = x : gamutNotation xs
gamutNotation [] = []

gamutMPNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutMPNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }

gamutIPNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutIPNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }

gamutPNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutPNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }

gamutPNDPlusCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutPNDPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser gamutOpts)
    , ndParseForm = purePropFormulaParser gamutOpts
    , ndNotation = gamutNotation
    }
