{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Gamut (gamutNDCalc, parseGamutND) where

import Text.Parsec
import Data.Char
import Carnap.Core.Data.Types (Form, Term)
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
import Carnap.Languages.PurePropositional.Logic.Gamut
import Carnap.Languages.PurePropositional.Logic.Rules

data GamutND = ND GamutPND
             | InE
             | ElimE
             | InA
             | ElimA

    deriving Eq

instance Show GamutND where
        show (ND x) = show x
        show InE = "I∃"
        show ElimE = "E∃"
        show InA = "I∀"
        show ElimA = "E∀"

instance Inference GamutND PureLexiconFOL (Form Bool) where

        ruleOf InE = existentialGeneralization
        ruleOf InA = universalGeneralization
        ruleOf ElimA = universalInstantiation
        ruleOf ElimE = conditionalExistentialDerivation
        ruleOf r = premisesOf r ∴ conclusionOf r

        premisesOf (ND x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf (ND x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        indirectInference (ND x) = indirectInference x
        indirectInference _ = Nothing

        restriction InA        = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
        restriction ElimE      = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        restriction _          = Nothing

        globalRestriction (Left ded) n InA   = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction (Left ded) n ElimE = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
        globalRestriction (Left ded) n (ND (IPND (MPND InIf1))) = Just $ fitchAssumptionCheck n ded [(phin 1, phin 2)]
        globalRestriction (Left ded) n (ND (IPND (MPND InIf2))) = Just $ fitchAssumptionCheck n ded [(phin 1, phin 2)]
        globalRestriction (Left ded) n (ND (IPND (MPND InNeg1))) = Just $ fitchAssumptionCheck n ded [(phin 1, lfalsum)]
        globalRestriction (Left ded) n (ND (IPND (MPND InNeg2))) = Just $ fitchAssumptionCheck n ded [(phin 1, lfalsum)]
        globalRestriction _ _ _ = Nothing

        isAssumption (ND x) = isAssumption x
        isAssumption _ = False

parseGamutND rtc = try propRule <|> quantRule
    where propRule = map ND <$> parseGamutPND rtc
          quantRule = do r <- choice (map (try . string) [ "IA", "I∀", "EA", "E∀", "IE", "I∃", "EE", "E∃" ])
                         case r of
                             r | r `elem` [ "IA", "I∀" ] -> return [InA]
                               | r `elem` [ "EA", "E∀" ] -> return [ElimA]
                               | r `elem` [ "IE", "I∃" ] -> return [InE]
                               | r `elem` [ "EE", "E∃" ] -> return [ElimE]

parseGamutNDProof :: RuntimeNaturalDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine GamutND PureLexiconFOL (Form Bool)]
parseGamutNDProof rtc = toDeductionFitch (parseGamutND rtc) (gamutNDFormulaParser)

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
