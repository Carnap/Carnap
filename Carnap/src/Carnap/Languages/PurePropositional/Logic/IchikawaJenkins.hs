{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.IchikawaJenkins
    ( parseIchikawaJenkinsSL, IchikawaJenkinsSL,  ichikawaJenkinsSLCalc, ichikawaJenkinsSLTableauCalc, IchikawaJenkinsSLTableaux(..), IchikawaJenkinsSL(..)) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Core.Unification.Unification
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Logic.Magnus
import Carnap.Calculi.Util
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Util
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.Util.LanguageClasses
import Control.Lens

-------------------------
--  Natural Deduction  --
-------------------------

newtype IchikawaJenkinsSL = IJ MagnusSLPlus deriving Eq

instance Show IchikawaJenkinsSL where
        show (IJ (MSL CondIntro1)) = "⊃I"
        show (IJ (MSL CondIntro2)) = "⊃I"
        show (IJ (MSL CondElim))   = "⊃E"
        show (IJ (MSL BicoIntro1)) = "≡I"
        show (IJ (MSL BicoIntro2)) = "≡I"
        show (IJ (MSL BicoIntro3)) = "≡I"
        show (IJ (MSL BicoIntro4)) = "≡I"
        show (IJ (MSL BicoElim1))  = "≡E"
        show (IJ (MSL BicoElim2))  = "≡E"
        show (IJ BiExRep) = "≡ex"
        show (IJ RepBiEx) = "≡ex"
        show (IJ x) = show x

instance Inference IchikawaJenkinsSL PurePropLexicon (Form Bool) where
        ruleOf (IJ (MSL BicoIntro1)) = biconditionalProofVariations !! 0
        ruleOf (IJ (MSL BicoIntro2)) = biconditionalProofVariations !! 1
        ruleOf (IJ (MSL BicoIntro3)) = biconditionalProofVariations !! 2
        ruleOf (IJ (MSL BicoIntro4)) = biconditionalProofVariations !! 3
        ruleOf (IJ x) = ruleOf x

        indirectInference (IJ (MSL x)) 
            | x `elem` [ BicoIntro1, BicoIntro2
                       , BicoIntro3, BicoIntro4] = Just PolyProof
        indirectInference (IJ (MSL x)) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (IJ x) = isAssumption x

        isPremise (IJ x) = isPremise x

        restriction (IJ x) = restriction x

parseIchikawaJenkinsSL :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [IchikawaJenkinsSL]
parseIchikawaJenkinsSL rtc = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI",">I","->I","⊃I","CE",">E", "->E", "⊃E"
                                                         ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<>I","<->I", "≡I" 
                                                         , "BE", "<>E","<->E", "≡E", "R", "HYP","DIL","MT", "Comm", "DN", "MC", "≡ex", "<>ex", "<->ex", "DeM"])
                                                         <|> ((++) <$> string "A/" <*> many anyChar)
                                case r of
                                 r | r == "AS" -> fromMSL [As ""]
                                   | r == "PR" -> fromMSL [Pr (problemPremises rtc)]
                                   | r == "R"  -> fromMSL [Reiterate]
                                   | r `elem` ["&I","/\\I","∧I"] -> fromMSL [ConjIntro]
                                   | r `elem` ["&E","/\\E","∧E"] -> fromMSL [ConjElim1, ConjElim2]
                                   | r `elem` ["CI",">I", "->I","⊃I"]  -> fromMSL [CondIntro1,CondIntro2]
                                   | r `elem` ["CE",">E", "->E", "⊃E"] -> fromMSL [CondElim]
                                   | r `elem` ["~I","¬I","-I"]   -> fromMSL [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                                   | r `elem` ["~E","¬E","-E"]   -> fromMSL [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                                   | r `elem` ["vI","\\/I"]   -> fromMSL [DisjIntro1, DisjIntro2]
                                   | r `elem` ["vE","\\/E"]   -> fromMSL [DisjElim1, DisjElim2]
                                   | r `elem` ["BI","<>I","<->I","≡I"]   -> fromMSL [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                   | r `elem` ["BE","<>E","<->E","≡E"] -> fromMSL [BicoElim1, BicoElim2]
                                   | r == "HYP"  -> fromMSLPlus [Hyp]
                                   | r == "DIL"   -> fromMSLPlus [Dilemma]
                                   | r == "Comm"  -> fromMSLPlus [AndComm,CommAnd,OrComm,CommOr,IffComm,CommIff]
                                   | r == "DN"    -> fromMSLPlus [DNRep,RepDN]
                                   | r == "MC"    -> fromMSLPlus [MCRep,MCRep2,RepMC,RepMC2]
                                   | r `elem` ["≡ex", "<>ex", "<->ex"] -> fromMSLPlus [BiExRep,RepBiEx]
                                   | r == "DeM"   -> fromMSLPlus [DM1,DM2,DM3,DM4]
                                 'A':'/':rest -> fromMSL [As rest]
    where fromMSL = return . map (IJ . MSL)
          fromMSLPlus = return . map IJ

parseIchikawaJenkinsProof :: RuntimeNaturalDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine IchikawaJenkinsSL PurePropLexicon (Form Bool)]
parseIchikawaJenkinsProof rtc = toDeductionFitch (parseIchikawaJenkinsSL rtc) (purePropFormulaParser magnusOpts)

ichikawaJenkinsNotation :: String -> String 
ichikawaJenkinsNotation x = case runParser altparser 0 "" x of
                                    Left e -> show e
                                    Right s -> s
    where altparser = do s <- handlecon <|> try handleatom <|> handleLParen <|> handleRParen <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handlecon = (char '∧' >> return "&") 
                      <|> (char '→' >> return "⊃")
                      <|> (char '↔' >> return "≡")
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

ichikawaJenkinsSLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseIchikawaJenkinsProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser magnusOpts)
    , ndParseForm = purePropFormulaParser magnusOpts
    , ndNotation = ichikawaJenkinsNotation
    }

-------------------------
--  Semantic Tableaux  --
-------------------------

data IchikawaJenkinsSLTableaux = Ax1 | Ax2 | Conj | NConj | Disj | NDisj | Cond | NCond | Bicond | NBicond | DoubleNeg | Struct | Lit
    deriving Eq

instance Show IchikawaJenkinsSLTableaux where
    show Ax1= "Ax"
    show Ax2= "Ax"
    show Struct = "St"
    show Lit = "Lit"
    show Conj = "&"
    show NConj = "¬&"
    show Disj  = "∨"
    show NDisj = "¬∨"
    show Cond = "⊃" 
    show NCond = "¬⊃"
    show Bicond = "≡"
    show NBicond = "¬≡"
    show DoubleNeg = "¬¬"

parseIchikawaJenkinsSLTableaux :: Parsec String u [IchikawaJenkinsSLTableaux]
parseIchikawaJenkinsSLTableaux = do r <- choice (map (try . string) ["&","¬&","~&","-&"
                                                                ,"/\\","¬/\\","~/\\","-/\\"
                                                                ,"∨","¬∨","~∨","-∨"
                                                                , "v", "¬v","~v","-v"
                                                                , "\\/", "¬\\/","~\\/","-\\/"
                                                                , "⊃", "¬⊃","~⊃","-⊃"
                                                                , "->", "¬->","~->","-->"
                                                                , "->", "¬->","~->","-->"
                                                                , ">", "¬>","~>","->"
                                                                , "C", "¬C","~C","-C"
                                                                , "≡", "¬≡","~≡","-≡"
                                                                , "<->", "¬<->","~<->","-<->"
                                                                , "<>", "¬<>","~<>","-<>"
                                                                , "B", "¬B","~B","-B"
                                                                , "¬¬","~~","--"
                                                                , "Ax", "St", "Lit"
                                                                ])
                                    return $ case r of
                                       r | r `elem` ["&", "/\\"] -> [Conj]
                                         | r == "Ax" -> [Ax1,Ax2]
                                         | r `elem` ["¬&","~&","-&","¬/\\","~/\\","-/\\"] -> [NConj]
                                         | r `elem` ["∨","v","\\/"] -> [Disj]
                                         | r `elem` [ "¬∨","~∨","-∨", "¬\\/","~\\/","-\\/", "¬v","~v","-v"] -> [NDisj]
                                         | r `elem` ["⊃","->",">","C"] -> [Cond]
                                         | r `elem` [ "¬⊃","~⊃","-⊃", "¬>","~>","->", "¬->","~->","-->", "¬C","~C","-C"] -> [NCond]
                                         | r `elem` ["≡","<->","<>","B"] -> [Bicond]
                                         | r `elem` [ "¬≡","~≡","-≡", "¬<->","~<->","-<->", "¬<>","~<>","-<>", "¬B","~B","-B"] -> [NBicond]
                                         | r `elem` [ "¬¬","~~","--"] -> [DoubleNeg]
                                         | r `elem` [ "St" ] -> [Struct]
                                         | r `elem` [ "Lit" ] -> [Lit]

instance CoreInference IchikawaJenkinsSLTableaux PurePropLexicon (Form Bool) where
        corePremisesOf Conj = [SA (phin 1) :+: SA (phin 2) :+: GammaV 1 :|-: Bot]
        corePremisesOf NConj = [ SA (lneg $ phin 1) :+: GammaV 1 :|-: Bot
                               , SA (lneg $ phin 2) :+: GammaV 1 :|-: Bot
                               ]
        corePremisesOf Disj = [ SA (phin 1) :+: GammaV 1 :|-: Bot
                              , SA (phin 2) :+: GammaV 1 :|-: Bot
                              ]
        corePremisesOf NDisj = [SA (lneg $ phin 1) :+: SA (lneg $ phin 2) :+: GammaV 1 :|-: Bot]
        corePremisesOf Cond = [ SA (lneg $ phin 1) :+: GammaV 1 :|-: Bot
                              , SA (phin 2) :+: GammaV 1 :|-: Bot
                              ]
        corePremisesOf NCond = [SA (phin 1) :+: SA (lneg $ phin 2) :+: GammaV 1 :|-: Bot]
        corePremisesOf Bicond = [ SA (phin 1) :+: SA (phin 2) :+: GammaV 1 :|-: Bot
                                , SA (lneg $ phin 1) :+: SA (lneg $ phin 2) :+: GammaV 1 :|-: Bot
                                ]
        corePremisesOf NBicond = [ SA (phin 1) :+: SA (lneg $ phin 2) :+: GammaV 1 :|-: Bot
                                 , SA (lneg $ phin 1) :+: SA (phin 2) :+: GammaV 1 :|-: Bot
                                 ]
        corePremisesOf DoubleNeg = [ SA (phin 1)  :+: GammaV 1 :|-: Bot ]
        corePremisesOf Struct = [ GammaV 1 :|-: DeltaV 1 ]
        corePremisesOf Lit = []
        corePremisesOf Ax1 = []
        corePremisesOf Ax2 = []

        coreConclusionOf Conj = SA (phin 1 ./\. phin 2) :+: GammaV 1 :|-: Bot
        coreConclusionOf NConj = SA (lneg $ phin 1 ./\. phin 2 ) :+: GammaV 1 :|-: Bot
        coreConclusionOf Disj = SA (phin 1 .\/. phin 2) :+: GammaV 1 :|-: Bot
        coreConclusionOf NDisj = SA (lneg $ phin 2 .\/. phin 1) :+: GammaV 1 :|-: Bot
        coreConclusionOf Cond = SA (phin 1 .=>. phin 2) :+: GammaV 1 :|-: Bot
        coreConclusionOf NCond = SA (lneg $ phin 1 .=>. phin 2) :+: GammaV 1 :|-: Bot
        coreConclusionOf Bicond = SA (phin 2 .<=>. phin 1) :+: GammaV 1 :|-: Bot
        coreConclusionOf NBicond = SA (lneg $ phin 2 .<=>. phin 1) :+: GammaV 1 :|-: Bot
        coreConclusionOf DoubleNeg = SA (lneg $ lneg $ phin 1)  :+: GammaV 1 :|-: Bot
        coreConclusionOf Ax1 = SA (phin 1) :+: SA (lneg $ phin 1) :+: GammaV 1 :|-: Bot
        coreConclusionOf Ax2 = SA (lneg $ phin 1) :+: SA (phin 1) :+: GammaV 1 :|-: Bot
        coreConclusionOf Struct = GammaV 1 :|-: DeltaV 1
        coreConclusionOf Lit = GammaV 1 :|-: DeltaV 1

        coreRestriction Lit = Just $ \sub -> allLiterals (applySub sub $ coreConclusionOf Lit)
             where allLiterals :: forall lex . ( PrismBooleanConnLex (ClassicalSequentLexOver lex) Bool
                                               , Eq (ClassicalSequentOver lex (Form Bool))
                                               , HasLiterals (ClassicalSequentLexOver lex) Bool
                                               ) => ClassicalSequentOver lex (Sequent (Form Bool)) -> Maybe String
                   allLiterals (x:|-:_)= let theForms = toListOf concretes x :: [ClassicalSequentOver lex (Form Bool)]
                                         in if all isLiteral theForms && isContradictionFree theForms
                                            then Nothing
                                            else Just "To complete a branch with the literal rule, the sequent must consist entirely of literals and must be contradiction-free"

        coreRestriction _ = Nothing

ichikawaJenkinsSLTableauCalc = mkTBCalc
    { tbParseForm = purePropFormulaParser magnusOpts
    , tbParseRule = parseIchikawaJenkinsSLTableaux
    }
