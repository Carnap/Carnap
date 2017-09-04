{-#LANGUAGE  TypeOperators, FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Magnus (magnusQLCalc,parseMagnusQL) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.ClassicalSequent.Syntax
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
-- magnus

data MagnusQL = MagnusSL P.MagnusSL | UI | UE | EI | EE1 | EE2 | IDI | IDE1 | IDE2
                    deriving Eq

instance Show MagnusQL where
        show (MagnusSL x) = show x
        show UI          = "∀I"
        show UE          = "∀E"
        show EI          = "∃I"
        show EE1         = "∃E"
        show EE2         = "∃E"
        show IDI         = "=I"
        show IDE1        = "=E"
        show IDE2        = "=E"

instance Inference MagnusQL PureLexiconFOL (Form Bool) where

         ruleOf UI   = universalGeneralization
         ruleOf UE   = universalInstantiation
         ruleOf EI   = existentialGeneralization
         ruleOf EE1  = existentialDerivation !! 0 
         ruleOf EE2  = existentialDerivation !! 1 
         ruleOf IDI  = eqReflexivity

         ruleOf IDE1  = leibnizLawVariations !! 0
         ruleOf IDE2  = leibnizLawVariations !! 1

         premisesOf (MagnusSL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (MagnusSL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (MagnusSL x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1,EE2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UI    = Just (eigenConstraint (SeqT 1) (ss (PBind (All "v") $ phi 1)) (fogamma 1))
         restriction EE1   = Just (eigenConstraint (SeqT 1) (ss (PBind (Some "v") $ phi 1) :-: ss (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction EE2   = Nothing --Since this one does not use the assumption with a fresh object
         restriction _     = Nothing

         isAssumption (MagnusSL x) = isAssumption x
         isAssumption _ = False

parseMagnusQL ders = try liftProp <|> quantRule
    where liftProp = do r <- P.parseMagnusSL ders
                        return (map MagnusSL r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E" ])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UI]
                              | r `elem` ["∀E","AE"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃E","EE"] -> return [EE1, EE2]
                              | r == "=I" -> return [IDI]
                              | r == "=E" -> return [IDE1,IDE2]

parseMagnusQLProof ::  Map String P.DerivedRule -> String -> [DeductionLine MagnusQL PureLexiconFOL (Form Bool)]
parseMagnusQLProof ders = toDeductionFitch (parseMagnusQL ders) magnusFOLFormulaParser

magnusQLCalc = NaturalDeductionCalc
    { ndRenderer = FitchStyle
    , ndParseProof = parseMagnusQLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = folSeqParser
    }
