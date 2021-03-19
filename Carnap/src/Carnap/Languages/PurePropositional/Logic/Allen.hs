{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Allen
    ( parseAllenSL, parseAllenSLPlus, AllenSLPlus(..), allenSLPlusCalc, AllenSL(..),  allenSLCalc) where

import Data.Map as M (lookup, Map)
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
import Carnap.Languages.Util.LanguageClasses

{-| A system for propositional logic resembling the basic proof system in Allen and Hand's Logic Primer-}

data AllenSL =  Reiterate   | ConjIntro
              | ConjElim1   | ConjElim2
              | DisjIntro1  | DisjIntro2
              | DisjElim1   | DisjElim2
              | CondIntro1  | CondIntro2
              | CondElim
              | BicoIntro
              | BicoElim1   | BicoElim2
              | NegeIntro1  | NegeIntro2
              | NegeIntro3  | NegeIntro4
              | NegeElim1   | NegeElim2
              | NegeElim3   | NegeElim4
              | Reductio1   | Reductio2
              | Reductio3   | Reductio4
              | Reductio5   | Reductio6
              | Reductio7   | Reductio8
              | DNRep       | RepDN
              | As String
              | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
              deriving (Eq)
              --skipping derived rules for now

instance Show AllenSL where
        show ConjIntro  = "&I"
        show ConjElim1  = "&E"
        show ConjElim2  = "&E"
        show CondIntro1 = "→I"
        show CondIntro2 = "→I"
        show CondElim   = "→E"
        show NegeIntro1 = "¬I"
        show NegeIntro2 = "¬I"
        show NegeIntro3 = "¬I"
        show NegeIntro4 = "¬I"
        show NegeElim1  = "¬E" 
        show NegeElim2  = "¬E"
        show NegeElim3  = "¬E"
        show NegeElim4  = "¬E"
        show Reductio1  = "RAA"
        show Reductio2  = "RAA"
        show Reductio3  = "RAA"
        show Reductio4  = "RAA"
        show Reductio5  = "RAA"
        show Reductio6  = "RAA"
        show Reductio7  = "RAA"
        show Reductio8  = "RAA"
        show DisjElim1  = "∨E"
        show DisjElim2  = "∨E"
        show DisjIntro1 = "∨I"
        show DisjIntro2 = "∨I"
        show BicoIntro = "↔I"
        show BicoElim1  = "↔E"
        show BicoElim2  = "↔E"
        show Reiterate  = "R"
        show DNRep      = "DN"
        show RepDN      = "DN"
        show (As "")    = "AS"
        show (As s)     = s
        show (Pr _)     = "PR"

instance Inference AllenSL PurePropLexicon (Form Bool) where
        ruleOf Reiterate  = identityRule
        ruleOf ConjIntro  = adjunction
        ruleOf ConjElim1  = simplificationVariations !! 0
        ruleOf ConjElim2  = simplificationVariations !! 1
        ruleOf DisjIntro1 = additionVariations !! 0
        ruleOf DisjIntro2 = additionVariations !! 1 
        ruleOf DisjElim1  = modusTollendoPonensVariations !! 0
        ruleOf DisjElim2  = modusTollendoPonensVariations !! 1
        ruleOf CondIntro1 = conditionalProofVariations !! 0
        ruleOf CondIntro2 = conditionalProofVariations !! 1
        ruleOf CondElim   = modusPonens
        ruleOf BicoIntro  = conditionalToBiconditional
        ruleOf BicoElim1  = biconditionalPonensVariations !! 0
        ruleOf BicoElim2  = biconditionalPonensVariations !! 1
        ruleOf NegeIntro1 = explicitConstructiveReductioVariations !! 0
        ruleOf NegeIntro2 = explicitConstructiveReductioVariations !! 1
        ruleOf NegeIntro3 = explicitConstructiveReductioVariations !! 2
        ruleOf NegeIntro4 = explicitConstructiveReductioVariations !! 3
        ruleOf NegeElim1  = explicitNonConstructiveReductioVariations !! 0
        ruleOf NegeElim2  = explicitNonConstructiveReductioVariations !! 1
        ruleOf NegeElim3  = explicitNonConstructiveReductioVariations !! 2
        ruleOf NegeElim4  = explicitNonConstructiveReductioVariations !! 3
        ruleOf Reductio1  = explicitConstructiveReductioVariations !! 0
        ruleOf Reductio2  = explicitConstructiveReductioVariations !! 1
        ruleOf Reductio3  = explicitConstructiveReductioVariations !! 2
        ruleOf Reductio4  = explicitConstructiveReductioVariations !! 3
        ruleOf Reductio5  = explicitNonConstructiveReductioVariations !! 0
        ruleOf Reductio6  = explicitNonConstructiveReductioVariations !! 1
        ruleOf Reductio7  = explicitNonConstructiveReductioVariations !! 2
        ruleOf Reductio8  = explicitNonConstructiveReductioVariations !! 3
        ruleOf DNRep      = doubleNegation !! 0
        ruleOf RepDN      = doubleNegation !! 1
        ruleOf (As _)     = axiom
        ruleOf (Pr _)     = axiom

        indirectInference x
            | x `elem` [CondIntro1,CondIntro2] = Just PolyProof
            | x `elem` [ NegeIntro1, NegeIntro2 , NegeIntro3, NegeIntro4
                       , NegeElim1, NegeElim2, NegeElim3 , NegeElim4
                       , Reductio1, Reductio2, Reductio3, Reductio4
                       , Reductio5, Reductio6, Reductio7, Reductio8
                       ] = Just (TypedProof (ProofType 1 2))
            | otherwise = Nothing

        isAssumption (As _) = True
        isAssumption _ = False

        isPremise (Pr _) = True
        isPremise _ = False

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n CondIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n CondIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n NegeIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeIntro3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeIntro4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n NegeElim1  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n NegeElim2  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n NegeElim3  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n NegeElim4  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n Reductio1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n Reductio2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n Reductio3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n Reductio4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]  
        globalRestriction (Left ded) n Reductio5  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n Reductio6  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n Reductio7  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction (Left ded) n Reductio8  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])] 
        globalRestriction _ _ _ = Nothing

parseAllenSL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [AllenSL]
parseAllenSL rtc = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I","→E","CE","->E", "→E"
                                                         ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I" 
                                                         , "BE", "<->E", "↔E", "RAA", "R", "DN"]) <|> ((++) <$> string "A/" <*> many anyChar)
                      case r of
                            r | r == "AS" -> return [As ""]
                              | r == "PR" -> return [Pr (problemPremises rtc)]
                              | r == "R"  -> return [Reiterate]
                              | r == "DN" -> return [DNRep,RepDN]
                              | r == "RAA" -> return [Reductio1, Reductio2, Reductio3, Reductio4, Reductio5, Reductio6, Reductio7, Reductio8]
                              | r `elem` ["&I","/\\I","∧I"] -> return [ConjIntro]
                              | r `elem` ["&E","/\\E","∧E"] -> return [ConjElim1, ConjElim2]
                              | r `elem` ["CI","->I","→I"]  -> return [CondIntro1,CondIntro2]
                              | r `elem` ["CE","->E", "→E"] -> return [CondElim]
                              | r `elem` ["~I","¬I","-I"]   -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                              | r `elem` ["~E","¬E","-E"]   -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                              | r `elem` ["vI","\\/I"]   -> return [DisjIntro1, DisjIntro2]
                              | r `elem` ["vE","\\/E"]   -> return [DisjElim1, DisjElim2]
                              | r `elem` ["BI","<->I","↔I"]   -> return [BicoIntro]
                              | r `elem` ["BE","<->E","↔E"] -> return [BicoElim1, BicoElim2]
                            'A':'/':rest -> return [As (rest)]

parseAllenSLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine AllenSL PurePropLexicon (Form Bool)]
parseAllenSLProof rtc = toDeductionFitch (parseAllenSL rtc) (purePropFormulaParser magnusOpts)

allenNotation :: String -> String 
allenNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> s
    where altparser = do s <- handlecon <|> try handleatom <|> handleLParen <|> handleRParen <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handlecon = try (char '∧' >> return "&") 
                      <|> (char '⊤' >> return " ")
                      <|> (char '∅' >> return " ")
          handleatom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          handleLParen = do char '('
                            n <- getState 
                            putState (n + 1)
                            return $ ["(","["] !! (n `mod` 2) 
          handleRParen = do char ')'
                            n <- getState 
                            putState (n - 1)
                            return $ [")","]"] !! ((n - 1) `mod` 2)
          fallback = do c <- anyChar 
                        return [c]

allenSLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseAllenSLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser magnusOpts)
    , ndParseForm = purePropFormulaParser magnusOpts
    , ndNotation = allenNotation
    }

{-| A system for propositional logic resembling the basic 
proof system in Allen and Hand's Logic Primer, including some derived rules
-}
data AllenSLPlus = ASL AllenSL   | Hyp 
                  | Dilemma      | MT
                  --various replacement rules with their reverse
                  --directions included
                  | MCRep        | RepMC
                  | MCRep2       | RepMC2
                  --plus DeMorgans
                  | DM1 | DM2 | DM3 | DM4
    deriving Eq

instance Show AllenSLPlus where
        show (ASL x) = show x
        show Hyp     = "HS"
        show MT      = "MT"
        show Dilemma = "DIL"
        show MCRep   = "MC"
        show RepMC   = "MC"
        show MCRep2  = "MC"
        show RepMC2  = "MC"
        show DM1     = "DeM"
        show DM2     = "DeM"
        show DM3     = "DeM"
        show DM4     = "DeM"

instance Inference AllenSLPlus PurePropLexicon (Form Bool) where
        ruleOf (ASL x) = ruleOf x
        ruleOf Hyp     = hypotheticalSyllogism
        ruleOf MT      = modusTollens
        ruleOf Dilemma = dilemma
        ruleOf MCRep   = materialConditional !! 0
        ruleOf RepMC   = materialConditional !! 1
        ruleOf MCRep2  = materialConditional !! 2
        ruleOf RepMC2  = materialConditional !! 3

        ruleOf DM1    = deMorgansLaws !! 0
        ruleOf DM2    = deMorgansLaws !! 1
        ruleOf DM3    = deMorgansLaws !! 2
        ruleOf DM4    = deMorgansLaws !! 3

        globalRestriction (Left ded) n (ASL CondIntro1)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (ASL CondIntro2)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (ASL NegeIntro1)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL NegeIntro2)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL NegeIntro3)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL NegeIntro4)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL NegeElim1)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL NegeElim2)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL NegeElim3)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL NegeElim4)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio1)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio2)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio3)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio4)  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio5)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio6)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio7)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction (Left ded) n (ASL Reductio8)  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [phin 2, lneg $ phin 2])]
        globalRestriction _ _ _ = Nothing

        indirectInference (ASL x) = indirectInference x
        indirectInference _ = Nothing

        isPremise (ASL x) = isPremise x
        isPremise _ = False

        isAssumption (ASL x) = isAssumption x
        isAssumption _ = False

        restriction (ASL x) = restriction x
        restriction _ = Nothing

parseAllenSLPlus :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [AllenSLPlus]
parseAllenSLPlus rtc = try plus <|> basic
    where basic = map ASL <$> parseAllenSL rtc
          plus = do r <- choice (map (try . string) ["HYP","DIL","MT", "MC", "DeM"])
                    case r of
                        "HYP"   -> return [Hyp]
                        "DIL"   -> return [Dilemma]
                        "MT"    -> return [MT]
                        "MC"    -> return [MCRep,MCRep2,RepMC,RepMC2]
                        "DeM"   -> return [DM1,DM2,DM3,DM4]

parseAllenSLPlusProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine AllenSLPlus PurePropLexicon (Form Bool)]
parseAllenSLPlusProof rtc = toDeductionFitch (parseAllenSLPlus rtc) (purePropFormulaParser magnusOpts)

allenSLPlusCalc = mkNDCalc
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseAllenSLPlusProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser magnusOpts)
    , ndParseForm = purePropFormulaParser magnusOpts
    , ndNotation = allenNotation
    }
