{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gamut (gamutNDCalc, parseGamutND, gamutNDPlusCalc, parseGamutNDPlus) where

import Text.Parsec
import Data.Char
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,subst,FirstOrder)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.PurePropositional.Logic.Gamut
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser (parseSeqOver)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Gamut as G
import Carnap.Languages.PurePropositional.Logic.Rules (fitchAssumptionCheck)

data GamutNDCore =  InE | ElimE | InA | ElimA
        deriving Eq

data GamutND = ND GamutPND | Core GamutNDCore
    deriving Eq

data GamutNDPlus = NDP GamutPNDPlus
             | CoreP GamutNDCore
             | NC1 | NC2
             | DC1 | DC2
             | CP1 | CP2
             | CV1 | CV2
             | CV3 | CV4
             | Ba  | Ce
             | Da  | Fe
    deriving Eq

instance Show GamutNDCore where
        show InE = "I∃"
        show ElimE = "E∃"
        show InA = "I∀"
        show ElimA = "E∀"

instance Show GamutND where
        show (ND x) = show x
        show (Core x) = show x

instance Show GamutNDPlus where
        show (NDP x) = show x
        show (CoreP x) = show x
        show NC1 = "NC"
        show NC2 = "NC"
        show DC1 = "DC"
        show DC2 = "DC"
        show CP1 = "CP" 
        show CP2 = "CP" 
        show CV1 = "CV1" 
        show CV2 = "CV2" 
        show CV3 = "CV3" 
        show CV4 = "CV4" 
        show Ba  = "Ba"
        show Ce  = "Ce"
        show Da  = "Da"
        show Fe  = "Fe"

instance Inference GamutNDCore PureLexiconFOL (Form Bool) where

        ruleOf InE = existentialGeneralization
        ruleOf InA = universalGeneralization
        ruleOf ElimA = universalInstantiation
        ruleOf ElimE = conditionalExistentialDerivation

        premisesOf r = upperSequents (ruleOf r)

        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference _ = Nothing

        restriction InA        = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
        restriction ElimE      = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        restriction _          = Nothing

        globalRestriction (Left ded) n InA   = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction (Left ded) n ElimE = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction _ _ _ = Nothing

        isAssumption _ = False

instance Inference GamutND PureLexiconFOL (Form Bool) where
        ruleOf (Core x) = ruleOf x
        ruleOf r = premisesOf r ∴ conclusionOf r

        premisesOf (Core x) = premisesOf x
        premisesOf (ND x) = map liftSequent (premisesOf x)

        conclusionOf (Core x) = conclusionOf x
        conclusionOf (ND x) = liftSequent (conclusionOf x)

        indirectInference (ND x) = indirectInference x
        indirectInference _ = Nothing

        restriction (Core x) = restriction x
        restriction _          = Nothing

        globalRestriction (Left ded) n (Core InA)   = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction (Left ded) n (Core ElimE) = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction (Left ded) n (ND (IPND (MPND InIf1))) = Just $ fitchAssumptionCheck n ded [(phin 1, phin 2)]
        globalRestriction (Left ded) n (ND (IPND (MPND InIf2))) = Just $ fitchAssumptionCheck n ded [(phin 1, phin 2)]
        globalRestriction (Left ded) n (ND (IPND (MPND InNeg1))) = Just $ fitchAssumptionCheck n ded [(phin 1, lfalsum)]
        globalRestriction (Left ded) n (ND (IPND (MPND InNeg2))) = Just $ fitchAssumptionCheck n ded [(phin 1, lfalsum)]
        globalRestriction _ _ _ = Nothing

        isAssumption (ND x) = isAssumption x
        isAssumption _ = False

instance Inference GamutNDPlus PureLexiconFOL (Form Bool) where
        ruleOf (CoreP x) = ruleOf x
        ruleOf NC1 = negatedConditional !! 0 
        ruleOf NC2 = negatedConditional !! 1
        ruleOf DC1 = materialConditional !! 0
        ruleOf DC2 = materialConditional !! 0
        ruleOf CP1 = contraposition !! 0
        ruleOf CP2 = contraposition !! 1
        ruleOf (NDP DN1) = doubleNegation !! 0
        ruleOf (NDP DN2) = doubleNegation !! 1
        ruleOf (NDP LCC) = andCommutativity !! 0
        ruleOf (NDP LCD) = orCommutativity !! 0
        ruleOf (NDP LAC1) = andAssociativity !! 0
        ruleOf (NDP LAC2) = andAssociativity !! 1
        ruleOf (NDP LAD1) = orAssociativity !! 0 
        ruleOf (NDP LAD2) = orAssociativity !! 1
        ruleOf (NDP LDD1) = orDistributivity !! 0
        ruleOf (NDP LDD2) = orDistributivity !! 1
        ruleOf (NDP LDC1) = andDistributivity !! 0
        ruleOf (NDP LDC2) = andDistributivity !! 1
        ruleOf (NDP DMOR1) = deMorgansLaws !! 0
        ruleOf (NDP DMOR2) = deMorgansLaws !! 1
        ruleOf (NDP DMAND1) = deMorgansLaws !! 2
        ruleOf (NDP DMAND2) = deMorgansLaws !! 3
        ruleOf CV1 = [ GammaV 1 :|-: SS (lsome "v" (\x -> phi 1 x ./\. phi 2 x)) 
                     ] ∴ GammaV 1 :|-: SS (lsome "v" (\x -> phi 2 x ./\. phi 1 x))
        ruleOf CV2 = [ GammaV 1 :|-: SS (lneg $ lsome "v" (\x -> phi 1 x ./\. phi 2 x)) 
                     ] ∴ GammaV 1 :|-: SS (lneg $ lsome "v" (\x -> phi 2 x ./\. phi 1 x))
        ruleOf CV3 = [ GammaV 1 :|-: SS (lneg $ lsome "v" (\x -> phi 1 x ./\. phi 2 x)) 
                     ] ∴ GammaV 1 :|-: SS (lall "v" (\x -> phi 1 x .=>. lneg (phi 2 x)))
        ruleOf CV4 = [ GammaV 1 :|-: SS (lall "v" (\x -> phi 1 x .=>. phi 2 x))
                     , GammaV 2 :|-: SS (lsome "v" $ phi 1 )
                     ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lsome "v" (\x -> phi 1 x ./\. phi 2 x))
        ruleOf Ba = [ GammaV 1 :|-: SS (lall "v" (\x -> phi 1 x .=>. phi 2 x))
                    , GammaV 2 :|-: SS (lall "v" (\x -> phi 2 x .=>. phi 3 x))
                    ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lall "v" (\x -> phi 1 x .=>. phi 3 x))
        ruleOf Ce = [ GammaV 1 :|-: SS (lneg $ lsome "v" (\x -> phi 1 x ./\. phi 2 x))
                    , GammaV 2 :|-: SS (lall "v" (\x -> phi 3 x .=>. phi 1 x))
                    ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ lsome "v" (\x -> phi 3 x ./\. phi 2 x))
        ruleOf Da = [ GammaV 1 :|-: SS (lall "v" (\x -> phi 1 x .=>. phi 2 x))
                    , GammaV 2 :|-: SS (lsome "v" (\x -> phi 3 x ./\. phi 1 x))
                    ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lsome "v" (\x -> phi 3 x ./\. phi 2 x))
        ruleOf Fe = [ GammaV 1 :|-: SS (lneg $ lsome "v" (\x -> phi 1 x ./\. phi 2 x))
                    , GammaV 2 :|-: SS (lsome "v" (\x -> phi 3 x ./\. phi 1 x))
                    ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lsome "v" (\x -> phi 3 x ./\. (lneg $ phi 2 x)))
        ruleOf r = premisesOf r ∴ conclusionOf r

        premisesOf (CoreP x) = premisesOf x
        premisesOf (NDP r) | r `elem` replacements = upperSequents (ruleOf (NDP r))
            where replacements = [ DN1, DN2, LCC, LCD, LAC1, LAC2, LAD1, LAD2
                                 , LDD1, LDD2, LDC1, LDC2, DMOR1, DMOR2, DMAND1, DMAND2]
        premisesOf (NDP x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf (CoreP x) = conclusionOf x
        conclusionOf (NDP r) | r `elem` replacements = lowerSequent (ruleOf (NDP r))
            where replacements = [ DN1, DN2, LCC, LCD, LAC1, LAC2, LAD1, LAD2
                                 , LDD1, LDD2, LDC1, LDC2, DMOR1, DMOR2, DMAND1, DMAND2]
        conclusionOf (NDP x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference (NDP x) = indirectInference x
        indirectInference _ = Nothing

        restriction (CoreP x) = restriction x
        restriction _          = Nothing

        globalRestriction (Left ded) n (CoreP InA)   = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction (Left ded) n (CoreP ElimE) = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction (Left ded) n (NDP (PND (IPND (MPND InIf1)))) = Just $ fitchAssumptionCheck n ded [(phin 1, phin 2)]
        globalRestriction (Left ded) n (NDP (PND (IPND (MPND InIf2)))) = Just $ fitchAssumptionCheck n ded [(phin 1, phin 2)]
        globalRestriction (Left ded) n (NDP (PND (IPND (MPND InNeg1)))) = Just $ fitchAssumptionCheck n ded [(phin 1, lfalsum)]
        globalRestriction (Left ded) n (NDP (PND (IPND (MPND InNeg2)))) = Just $ fitchAssumptionCheck n ded [(phin 1, lfalsum)]
        globalRestriction _ _ _ = Nothing

        isAssumption (NDP x) = isAssumption x
        isAssumption _ = False

parseGamutNDCore rtc = do r <- choice (map (try . string) [ "IA", "I∀", "EA", "E∀", "IE", "I∃", "EE", "E∃" ])
                          case r of
                              r | r `elem` [ "IA", "I∀" ] -> return [InA]
                                | r `elem` [ "EA", "E∀" ] -> return [ElimA]
                                | r `elem` [ "IE", "I∃" ] -> return [InE]
                                | r `elem` [ "EE", "E∃" ] -> return [ElimE]

parseGamutND rtc = try propRule <|> quantRule
    where propRule = map ND <$> parseGamutPND rtc
          quantRule = map Core <$> parseGamutNDCore rtc

parseGamutNDPlus rtc = try propRule <|> try quantRule <|> plusRule
    where propRule = map NDP <$> parseGamutPNDPlus rtc
          quantRule = map CoreP <$> parseGamutNDCore rtc
          plusRule = do r <- choice (map (try . string) ["NC","DC","CP","CV1","CV2","CV3","CV4","Ba","Ce","Da","Fe" ])
                        case r of
                             "NC" -> return [NC1,NC2]
                             "DC" -> return [DC1,DC2]
                             "CP" -> return [CP1,CP2]
                             "CV1" -> return [CV1]
                             "CV2" -> return [CV2]
                             "CV3" -> return [CV3]
                             "CV4" -> return [CV4]
                             "Ba" -> return [Ba]
                             "Ce" -> return [Ce]
                             "Da" -> return [Da]
                             "Fe" -> return [Fe]

parseGamutNDProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GamutND PureLexiconFOL (Form Bool)]
parseGamutNDProof rtc = toDeductionFitch (parseGamutND rtc) (gamutNDFormulaParser)

parseGamutNDPlusProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GamutNDPlus PureLexiconFOL (Form Bool)]
parseGamutNDPlusProof rtc = toDeductionFitch (parseGamutNDPlus rtc) (gamutNDFormulaParser)

gamutNotation :: String -> String
gamutNotation (x:xs) = if x `elem` ['A' .. 'Z'] then x : trimParens 0 xs else x : gamutNotation xs
    where trimParens 0 ('(':xs) = trimParens 1 xs
          trimParens 1 (')':xs) = gamutNotation xs
          trimParens 1 (',':xs) = trimParens 1 xs
          trimParens n ('(':xs) = '(' : trimParens (n + 1) xs
          trimParens n (')':xs) = ')' : trimParens (n - 1) xs
          trimParens n (x:xs) = x : trimParens n xs
          trimParens n [] = []
gamutNotation x = x

gamutNDCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutNDProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gamutNDFormulaParser
    , ndParseForm = gamutNDFormulaParser
    , ndNotation = gamutNotation
    }

gamutNDPlusCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutNDPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gamutNDFormulaParser
    , ndParseForm = gamutNDFormulaParser
    , ndNotation = gamutNotation
    }
