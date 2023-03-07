{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureSecondOrder.Logic.Gamut (gamutNDSOLCalc) where

import Carnap.Core.Data.Types
import Carnap.Languages.PureSecondOrder.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint)
import Carnap.Languages.PureFirstOrder.Logic.Rules (notAssumedConstraint)
import Carnap.Languages.PureFirstOrder.Logic (GamutNDCore(..), GamutNDPlus(CoreP), parseGamutNDPlus)
import Carnap.Languages.PureSecondOrder.Parser (gamutFormulaParser)
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitch, hoProcessLineFitchMemo)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Text.Parsec
import Carnap.Languages.PureSecondOrder.Logic.Rules 

data GamutNDSOL = ABS Int             | APP Int 
                | InESOL Int          | ElimESOL Int 
                | InASOL Int          | ElimASOL Int 
                | GamutFO GamutNDPlus | PPR (Maybe [(ClassicalSequentOver PolyadicallySOLLex (Sequent (Form Bool)))])
    deriving (Eq)

instance Show GamutNDSOL where
        show (PPR _)      = "PR"
        show (ABS n)      = "ABS" ++ show n
        show (APP n)      = "APP" ++ show n
        show (InESOL n)   = "I∃"  ++ show n
        show (ElimESOL n) = "E∃"  ++ show n
        show (InASOL n)   = "I∀"  ++ show n
        show (ElimASOL n) = "E∀"  ++ show n
        show (GamutFO x)  = show x

sogamma :: Int -> ClassicalSequentOver PolyadicallySOLLex (Antecedent (Form Bool))
sogamma = GammaV

instance Inference GamutNDSOL PolyadicallySOLLex (Form Bool) where
        ruleOf (PPR _) = [] ∴ SA (phin 1) :|-: SS (phin 1)
        ruleOf (ABS n) = polyadicAbstraction n
        ruleOf (APP n) = polyadicApplication n
        ruleOf (InESOL n)   = polyadicExistentialGeneralization n
        ruleOf (InASOL n) = polyadicUniversalGeneralization n
        ruleOf (ElimASOL n) = polyadicUniversalInstantiation n
        ruleOf (ElimESOL n) = polyadicConditionalExistentialDerivation n

        premisesOf (GamutFO x) = map liftSequent (premisesOf x)
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf (GamutFO x) = liftSequent (conclusionOf x)
        conclusionOf r = lowerSequent (ruleOf r)

        restriction (PPR prems) = Just (premConstraint prems)

        restriction (InASOL n)  = 
            Just (psopredicateEigenConstraint (liftToSequent $ psolAppScheme (n - 1)) (ss' $ universalScheme n)  (sogamma 1))
        restriction (ElimESOL n)  = 
            Just (psopredicateEigenConstraint (liftToSequent $ psolAppScheme (n - 1)) (ss' $ existentialScheme n)  (sogamma 1 :+: sogamma 2))
        restriction (GamutFO (CoreP InA)) = 
            Just (eigenConstraint stau (ss' $ lall "v" phi) (sogamma 1))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent taup
        restriction (GamutFO (CoreP ElimE)) = 
            Just (eigenConstraint stau (ss' $ lsome "v" phi) (sogamma 1 :+: sogamma 2))
            where phi x = SOPhi 1 AOne AOne :!$: x
                  stau = liftToSequent taup
        restriction _ = Nothing
            
        indirectInference (GamutFO x) = indirectInference x
        indirectInference _ = Nothing

        globalRestriction (Left ded) n (InASOL m) = Just (notAssumedConstraint n ded (liftToSequent $ psolAppScheme (n - 1)))
        globalRestriction (Left ded) n (ElimESOL m) = Just (notAssumedConstraint n ded (liftToSequent $ psolAppScheme (n - 1)))
        globalRestriction _ _ _ = Nothing

        isAssumption (GamutFO x) = isAssumption x
        isAssumption _ = False

parseGamutNDSOL :: RuntimeDeductionConfig PolyadicallySOLLex (Form Bool)
                    -> Parsec String u [GamutNDSOL]
parseGamutNDSOL rtc = try soRule <|> liftFO
    where liftFO = do r <- parseGamutNDPlus (defaultRuntimeDeductionConfig)
                      return (map GamutFO r)
          soRule = do r <- choice (map (try . string) ["PR", "IA", "I∀", "EA", "E∀", "IE", "I∃", "EE", "∃E", "ABS", "APP"])
                      if r == "PR" 
                          then return [PPR $ problemPremises rtc]
                          else do ds <- many1 digit
                                  let n = read ds :: Int
                                  case r of 
                                        r | r `elem` ["IA", "I∀"] -> return [InASOL n]
                                          | r `elem` ["EA", "E∀"] -> return [ElimASOL n]
                                          | r `elem` ["IE", "I∃"] -> return [InESOL n]
                                          | r `elem` ["EE", "E∃"] -> return [ElimESOL n]
                                          | r == "ABS"  -> return [ABS n]
                                          | r == "APP"  -> return [APP n]

parseGamutNDSOLProof :: RuntimeDeductionConfig PolyadicallySOLLex (Form Bool) 
                    -> String -> [DeductionLine GamutNDSOL PolyadicallySOLLex (Form Bool)]
parseGamutNDSOLProof rtc = toDeductionFitch (parseGamutNDSOL rtc) gamutFormulaParser

gamutNotation :: String -> String
gamutNotation s = case s of
         (']':'(':xs) ->  ']' : trimParens 0 ('(':xs)
         ('∀':x:y:xs) | x `elem` ['A' .. 'Z'] -> '∀' : x: y : gamutNotation xs
         ('∃':x:y:xs) | x `elem` ['A' .. 'Z'] -> '∃' : x: y : gamutNotation xs
         (x:y:xs) | x `elem` ['A' .. 'Z'] && y `elem` ['0' .. '9'] -> x : y : trimParens 0 xs
         (x:xs)   | x `elem` ['A' .. 'Z'] -> x : trimParens 0 xs
         (x:xs) -> x : gamutNotation xs
         x -> x
    where trimParens 0 ('(':xs) = trimParens 1 xs
          trimParens 0 xs = gamutNotation xs
          trimParens 1 (')':xs) = gamutNotation xs
          trimParens 1 (',':xs) = trimParens 1 xs
          trimParens n ('(':xs) = '(' : trimParens (n + 1) xs
          trimParens n (')':xs) = ')' : trimParens (n - 1) xs
          trimParens n (x:xs) | x `elem` ['A' .. 'Z'] = x : trimParens n (trimParens 0 xs)
          trimParens n (x:xs) = x : trimParens n xs
          trimParens n [] = []

gamutNDSOLCalc = mkNDCalc
    { ndRenderer = NoRender
    , ndParseProof = parseGamutNDSOLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver gamutFormulaParser
    , ndParseForm = gamutFormulaParser
    , ndNotation = gamutNotation
    }
