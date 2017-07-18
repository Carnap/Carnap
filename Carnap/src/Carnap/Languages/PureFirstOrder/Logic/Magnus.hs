{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Magnus (forallxQLCalc,parseForallxQL) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConnectives
import Carnap.Languages.PureFirstOrder.Logic.Rules

--------------------
--  3. System QL  --
--------------------
-- A system of first-order logic resembling system QL from PD Magnus'
-- forallx

data ForallxQL = MagnusSL P.MagnusSL | UIX | UEX | EIX | EE1X | EE2X | IDIX | IDE1X | IDE2X
                    deriving Eq

instance Show ForallxQL where
        show (MagnusSL x) = show x
        show UIX          = "∀I"
        show UEX          = "∀E"
        show EIX          = "∃I"
        show EE1X         = "∃E"
        show EE2X         = "∃E"
        show IDIX         = "=I"
        show IDE1X        = "=E"
        show IDE2X        = "=E"

instance Inference ForallxQL PureLexiconFOL where

         ruleOf UIX   = universalInstantiation
         ruleOf UEX   = universalInstantiation
         ruleOf EIX   = existentialGeneralization
         ruleOf EE1X  = existentialDerivation !! 0 
         ruleOf EE2X  = existentialDerivation !! 1 
         ruleOf IDIX  = eqReflexivity

         ruleOf IDE1X  = leibnizLawVariations !! 0
         ruleOf IDE2X  = leibnizLawVariations !! 1

         premisesOf (MagnusSL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (MagnusSL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (MagnusSL x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1X,EE2X ] = Just AssumptiveProof
            | otherwise = Nothing

         restriction UIX    = Just (eigenConstraint (SeqT 1) (ss (PBind (All "v") $ phi 1)) (GammaV 1))
         restriction EE1X   = Just (eigenConstraint (SeqT 1) (ss (PBind (Some "v") $ phi 1) :-: ss (phin 1)) (GammaV 1 :+: GammaV 2))
         restriction EE2X   = Nothing --Since this one does not use the assumption with a fresh object
         restriction _      = Nothing

         isAssumption (MagnusSL x) = isAssumption x
         isAssumption _ = False

parseForallxQL ders = try liftProp <|> quantRule
    where liftProp = do r <- P.parseMagnusSL ders
                        return (map MagnusSL r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E" ])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UIX]
                              | r `elem` ["∀E","AE"] -> return [UEX]
                              | r `elem` ["∃I","EI"] -> return [EIX]
                              | r `elem` ["∃E","EE"] -> return [EE1X, EE2X]
                              | r == "=I" -> return [IDIX]
                              | r == "=E" -> return [IDE1X,IDE2X]

parseForallxQLProof ::  Map String P.DerivedRule -> String -> [DeductionLine ForallxQL PureLexiconFOL (Form Bool)]
parseForallxQLProof ders = toDeductionFitch (parseForallxQL ders) forallxFOLFormulaParser

forallxQLCalc = NaturalDeductionCalc
    { ndRenderer = FitchStyle
    , ndParseProof = parseForallxQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = folSeqParser
    }
