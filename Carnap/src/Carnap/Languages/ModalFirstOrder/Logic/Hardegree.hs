{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.ModalFirstOrder.Logic.Hardegree 
    (hardegreeMPLCalc,parseHardegreeMPL) 
where

import Text.Parsec
import qualified Data.Map as M
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.ModalFirstOrder.Syntax
import Carnap.Languages.ModalFirstOrder.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineHardegreeMemo, hoProcessLineHardegree)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.ModalFirstOrder.Logic.Rules
import Carnap.Languages.ModalPropositional.Logic.Hardegree
import Carnap.Languages.PurePropositional.Logic.Hardegree (hardegreeNotation)

data HardegreeMPLOver a = ModalProp a | UI | UE | EI | EE 
                 | QN1 | QN2 | QN3 | QN4
                 | NUO | NEO
                 deriving Eq

instance Show a => Show (HardegreeMPLOver a) where
        show (ModalProp x) = show x
        show UI          = "UD"
        show UE          = "∀O"
        show EI          = "∃I"
        show EE          = "∃O"
        show QN1         = "QN"
        show QN2         = "QN"
        show QN3         = "QN"
        show QN4         = "QN"
        show NUO         = "~∀O"
        show NEO         = "~∃O"

type HardegreeMPL = HardegreeMPLOver HardegreeK
                                
instance Inference HardegreeMPL IndexedModalFirstOrderLex (Form Bool) where

         ruleOf UI   = liftAbsRule $ universalGeneralization
         ruleOf UE   = liftAbsRule $ universalInstantiation
         ruleOf EI   = liftAbsRule $ existentialGeneralization
         ruleOf EE   = liftAbsRule $ existentialInstantiation
         ruleOf QN1  = liftAbsRule $ quantifierNegation !! 0
         ruleOf QN2  = liftAbsRule $ quantifierNegation !! 1
         ruleOf QN3  = liftAbsRule $ quantifierNegation !! 2
         ruleOf QN4  = liftAbsRule $ quantifierNegation !! 3
         ruleOf NUO  = liftAbsRule $ negatedUniversalInstantiation
         ruleOf NEO  = liftAbsRule $ negatedExistentialInstantiation

         premisesOf (ModalProp x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (ModalProp x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (ModalProp x) = indirectInference x
         indirectInference UI = Just (TypedProof (ProofType 0 1)) 
         indirectInference _ = Nothing

         globalRestriction (Left ded) n UE = Just (globalOldConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n EE = Just (globalNewConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n NEO = Just (globalOldConstraint [tau] (Left ded) n )
         globalRestriction (Left ded) n NUO = Just (globalNewConstraint [tau] (Left ded) n )
         --XXX: Would be nice to avoid this boilerplate, via some way of
         --lifting global constraints
         globalRestriction (Left ded) n (ModalProp (RelK DiaD1)) = Just (globalNewIdxConstraint [someWorld `indexcons` someOtherWorld] (Left ded) n )
         globalRestriction (Left ded) n (ModalProp (RelK DiaD2)) = Just (globalNewIdxConstraint [someWorld `indexcons` someOtherWorld] (Left ded) n )
         globalRestriction (Left ded) n (ModalProp (RelK DiaOut)) = Just (globalNewIdxConstraint [someWorld `indexcons` someOtherWorld] (Left ded) n )
         globalRestriction (Left ded) n (ModalProp (RelK ND)) = Just (globalNewIdxConstraint [someWorld `indexcons` someOtherWorld] (Left ded) n )
         globalRestriction (Left ded) n (ModalProp (RelK DiaIn)) = Just (globalOldIdxConstraint [someWorld `indexcons` someOtherWorld] (Left ded) n )
         globalRestriction (Left ded) n (ModalProp (RelK BoxOut)) = Just (globalOldIdxConstraint [someWorld `indexcons` someOtherWorld] (Left ded) n )
         globalRestriction (Left ded) n (ModalProp (RelK (MoPL FalO))) = Just (globalOldIdxConstraint [someOtherWorld,someWorld] (Left ded) n )
         globalRestriction (Left ded) n (ModalProp (RelK (MoPL FalI))) = Just (globalOldIdxConstraint [someOtherWorld,someWorld] (Left ded) n )
         globalRestriction (Left ded) n x = case indirectInference x of
                                                Nothing -> Just (globalOldIdxConstraint [someWorld] (Left ded) n)
                                                _ -> Nothing
         globalRestriction _ _ _ = Nothing

         isAssumption (ModalProp x) = isAssumption x
         isAssumption _ = False

parseHardegreeMPL ders = try liftK <|> quantRule
    where liftK = do r <- parseHardegreeK
                     return (map ModalProp r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI","UD", "∀O", "AO", "∃I", "EI"
                                                         , "∃O", "EO", "~∃O","-∃O" ,"-EO"
                                                         , "~EO","~∀O","~AO","-∀O","-AO" ])
                         case r of 
                            r | r `elem` ["∀I","AI","UD"] -> return [UI]
                              | r `elem` ["∀O","AO"] -> return [UE]
                              | r `elem` ["∃I","EI"] -> return [EI]
                              | r `elem` ["∃O","EO"] -> return [EE]
                              | r `elem` ["~∃O","-∃O" ,"-EO", "~EO"] -> return [NEO]
                              | r `elem` ["~∀O","~AO","-∀O","-AO"]   -> return [NUO]

parseHardegreeMPLProof ::  RuntimeDeductionConfig IndexedModalFirstOrderLex (Form Bool) -> String 
                            -> [DeductionLine HardegreeMPL IndexedModalFirstOrderLex (Form Bool)]
parseHardegreeMPLProof ders = toDeductionHardegree (parseHardegreeMPL ders) (hardegreeMPLFormulaParser)

hardegreeMPLCalc = mkNDCalc 
    { ndRenderer = MontagueStyle
    , ndParseProof = parseHardegreeMPLProof
    , ndProcessLine = hoProcessLineHardegree
    , ndProcessLineMemo = Just hoProcessLineHardegreeMemo
    , ndParseSeq = indexedModalFOSeqParser
    , ndNotation  = hardegreeNotation
    }
