{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Winkler (winklerFOLCalc) where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.Types (Form, Term)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitchMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.PureFirstOrder.Logic.Rules
import qualified Carnap.Languages.PurePropositional.Logic.Winkler as TFL
import Carnap.Languages.PurePropositional.Logic.Rules (premConstraint, fitchAssumptionCheck, axiom)

{-| A system for propositional logic resembling the basic proof system FOL
from the Winkler Remix of Forall x book
-}
data WinklerFOL = WinklerTFL TFL.WinklerTFL 
                | UnivIntro  | UnivElim
                | ExistIntro | ExistElim1 | ExistElim2
                | IdentIntro | IdentElim1 | IdentElim2
                | QN1 | QN2  | QN3 | QN4
                | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
        deriving (Eq)

instance Show WinklerFOL where
        show (WinklerTFL x) = show x
        show UnivIntro   = "∀I"
        show UnivElim    = "∀E"
        show ExistIntro  = "∃I"
        show ExistElim1  = "∃E"
        show ExistElim2  = "∃E"
        show IdentIntro  = "=I"
        show IdentElim1  = "=E"
        show IdentElim2  = "=E"
        show QN1         = "CQ"
        show QN2         = "CQ"
        show QN3         = "CQ"
        show QN4         = "CQ"
        show (Pr _)      = "PR"

instance Inference WinklerFOL PureLexiconFOL (Form Bool) where

         ruleOf QN1         = quantifierNegation !! 0 
         ruleOf QN2         = quantifierNegation !! 1
         ruleOf QN3         = quantifierNegation !! 2
         ruleOf QN4         = quantifierNegation !! 3
         ruleOf UnivIntro   = universalGeneralization
         ruleOf UnivElim    = universalInstantiation
         ruleOf ExistIntro  = existentialGeneralization
         ruleOf ExistElim2  = existentialDerivation !! 0 
         ruleOf ExistElim2  = existentialDerivation !! 1 
         ruleOf IdentIntro  = eqReflexivity
         ruleOf IdentElim1  = leibnizLawVariations !! 0
         ruleOf IdentElim2  = leibnizLawVariations !! 1
         ruleOf (WinklerTFL TFL.Com1)   = andCommutativity !! 0      
         ruleOf (WinklerTFL TFL.Com2)   = orCommutativity !! 0       
         ruleOf (WinklerTFL TFL.Assoc1) = andAssociativity !! 0      
         ruleOf (WinklerTFL TFL.Assoc2) = andAssociativity !! 1      
         ruleOf (WinklerTFL TFL.Assoc3) = orAssociativity !! 0       
         ruleOf (WinklerTFL TFL.Assoc4) = orAssociativity !! 1       
         ruleOf (WinklerTFL TFL.Impl1)  = materialConditional !! 0   
         ruleOf (WinklerTFL TFL.Impl2)  = materialConditional !! 1   
         ruleOf (WinklerTFL TFL.DN1)    = doubleNegation !! 0        
         ruleOf (WinklerTFL TFL.DN2)    = doubleNegation !! 1        
         ruleOf (WinklerTFL TFL.DeM1)   = deMorgansLaws !! 0         
         ruleOf (WinklerTFL TFL.DeM2)   = deMorgansLaws !! 1         
         ruleOf (WinklerTFL TFL.DeM3)   = deMorgansLaws !! 2         
         ruleOf (WinklerTFL TFL.DeM4)   = deMorgansLaws !! 3         
         ruleOf (WinklerTFL TFL.Idem1)  = andIdempotence !! 0        
         ruleOf (WinklerTFL TFL.Idem2)  = andIdempotence !! 1        
         ruleOf (WinklerTFL TFL.Idem3)  = orIdempotence !! 0         
         ruleOf (WinklerTFL TFL.Idem4)  = orIdempotence !! 1         
         ruleOf (WinklerTFL TFL.Trans1) = contraposition !! 0        
         ruleOf (WinklerTFL TFL.Trans2) = contraposition !! 1        
         ruleOf (WinklerTFL TFL.Exp1)   = exportation !! 0           
         ruleOf (WinklerTFL TFL.Exp2)   = exportation !! 1           
         ruleOf (WinklerTFL TFL.Dist1)  = distribution !! 0          
         ruleOf (WinklerTFL TFL.Dist2)  = distribution !! 1          
         ruleOf (WinklerTFL TFL.Dist3)  = distribution !! 4          
         ruleOf (WinklerTFL TFL.Dist4)  = distribution !! 5          
         ruleOf (WinklerTFL TFL.Equiv1) = biconditionalExchange !! 0 
         ruleOf (WinklerTFL TFL.Equiv2) = biconditionalExchange !! 1 
         ruleOf (WinklerTFL TFL.Equiv3) = biconditionalCases !! 0    
         ruleOf (WinklerTFL TFL.Equiv4) = biconditionalCases !! 1    
         ruleOf r@(WinklerTFL _) = premisesOf r ∴ conclusionOf r
         ruleOf (Pr _)      = axiom

         premisesOf (WinklerTFL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)

         conclusionOf (WinklerTFL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (WinklerTFL x) = indirectInference x
         indirectInference x  
            | x `elem` [ ExistElim1,ExistElim2 ] = Just assumptiveProof
            | otherwise = Nothing

         restriction UnivIntro = Just (eigenConstraint tau (SS $ lall "v" $ phi' 1) (fogamma 1))
         restriction ExistElim1 = Just (eigenConstraint tau ((SS $ lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction ExistElim2= Just (eigenConstraint tau ((SS $ lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
         restriction (Pr prems) = Just (premConstraint prems)
         restriction _     = Nothing

         globalRestriction (Left ded) n (WinklerTFL TFL.CondIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (WinklerTFL TFL.CondIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
         globalRestriction (Left ded) n (WinklerTFL TFL.BicoIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (WinklerTFL TFL.BicoIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (WinklerTFL TFL.BicoIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (WinklerTFL TFL.BicoIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
         globalRestriction (Left ded) n (WinklerTFL TFL.DisjElim1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (WinklerTFL TFL.DisjElim2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (WinklerTFL TFL.DisjElim3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (WinklerTFL TFL.DisjElim4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeIntro5) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lfalsum])]
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeIntro6) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lfalsum])]
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeElim1)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeElim2)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeElim3)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeElim4)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeElim5) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lfalsum])]
         globalRestriction (Left ded) n (WinklerTFL TFL.NegeElim6) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lfalsum])]
         globalRestriction (Left ded) n (WinklerTFL TFL.Tertium1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
         globalRestriction (Left ded) n (WinklerTFL TFL.Tertium2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
         globalRestriction (Left ded) n (WinklerTFL TFL.Tertium3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
         globalRestriction (Left ded) n (WinklerTFL TFL.Tertium4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([lneg $ phin 1], [phin 2])]
         globalRestriction _ _ _ = Nothing
         globalRestriction (Left ded) n UnivIntro = Just (notAssumedConstraint n ded (taun 1 :: FOLSequentCalc (Term Int)))
         globalRestriction (Left ded) n r | r `elem` [ExistElim1,ExistElim2] = 
             case dependencies (ded !! (n - 1)) of
               Just ls -> firstDistinct ls
               Nothing -> Nothing
             where firstDistinct [] = Nothing
                   firstDistinct ((a,b):xs) | a /= b = Just (notAssumedConstraint a ded (taun 1 :: FOLSequentCalc (Term Int)))
                                            | otherwise = firstDistinct xs

         isAssumption (WinklerTFL x) = isAssumption x
         isAssumption _ = False

         isPremise (Pr _) = True
         isPremise _ = False

parseWinklerFOL :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [WinklerFOL]
parseWinklerFOL rtc = try quantRule <|> (map WinklerTFL <$> parseProp)
    where parseProp = TFL.parseWinklerTFL (defaultRuntimeDeductionConfig)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E","CQ", "PR"])
                         return $ case r of 
                            r | r `elem` ["∀I","AI"] -> [UnivIntro]
                              | r `elem` ["∀E","AE"] -> [UnivElim]
                              | r `elem` ["∃I","EI"] -> [ExistIntro]
                              | r `elem` ["∃E","EE"] -> [ExistElim1, ExistElim2]
                              | r == "=I" -> [IdentIntro]
                              | r == "=E" -> [IdentElim1,IdentElim2]
                              | r == "PR" -> [Pr (problemPremises rtc)]
                              | r == "CQ" -> [QN1,QN2,QN3,QN4]

parseWinklerFOLProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine WinklerFOL PureLexiconFOL (Form Bool)]
parseWinklerFOLProof rtc = toDeductionFitch (parseWinklerFOL rtc) thomasBolducAndZachFOLFormulaParser

winklerFOLNotation :: String -> String 
winklerFOLNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- try handleCon <|> try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          handleCon = (char '∧' >> return "&") 
                      <|> (char '¬' >> return "~") 
                      <|> (char '→' >> return "⊃")
                      <|> (char '↔' >> return "≡")
                      <|> (char '⊤' >> return "")
          fallback = do c <- anyChar 
                        return [c]

winklerFOLCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseWinklerFOLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOLFormulaParser
    , ndParseForm = thomasBolducAndZachFOLFormulaParser
    , ndNotation = winklerFOLNotation
    }
