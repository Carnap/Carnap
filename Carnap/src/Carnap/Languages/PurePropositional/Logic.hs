{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic 
    (parsePropLogic, parseFitchPropLogic, parsePropProof, parseFitchPropProof, LogicBookPropLogic,
    DerivedRule(..), propSeqParser, PropSequentCalc) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Util
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type PropSequentCalc = ClassicalSequentOver PurePropLexicon

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema PropSequentCalc

pattern SeqP x arity      = FX (Lx2 (Lx1 (Predicate x arity)))
pattern SeqSP x arity     = FX (Lx2 (Lx2 (Predicate x arity)))
pattern SeqCon x arity    = FX (Lx2 (Lx3 (Connective x arity)))
pattern SeqProp n         = SeqP (Prop n) AZero
pattern SeqPhi n          = SeqSP (SProp n) AZero
pattern SeqAnd            = SeqCon And ATwo
pattern SeqOr             = SeqCon Or ATwo
pattern SeqIf             = SeqCon If ATwo
pattern SeqIff            = SeqCon Iff ATwo
pattern SeqNot            = SeqCon Not AOne
pattern (:&-:) x y        = SeqAnd :!$: x :!$: y
pattern (:||-:) x y       = SeqOr  :!$: x :!$: y
pattern (:->-:) x y       = SeqIf  :!$: x :!$: y
pattern (:<->-:) x y      = SeqIff :!$: x :!$: y
pattern SeqNeg x          = SeqNot :!$: x

data PropSeqLabel = PropSeqFO | PropSeqACUI
        deriving (Eq, Ord, Show)

instance Eq (PropSequentCalc a) where
        (==) = (=*)

instance Combineable PropSequentCalc PropSeqLabel where

    getLabel Top               = PropSeqACUI
    getLabel (_ :+: _)         = PropSeqACUI
    getLabel (GammaV _)        = PropSeqACUI
    --getLabel (SA     _)        = PropSeqACUI
    getLabel _                 = PropSeqFO

    getAlgo PropSeqFO   = foUnifySys
    getAlgo PropSeqACUI = acuiUnifySys

    replaceChild (_ :&-: x)   pig 0 = unEveryPig pig :&-: x
    replaceChild (x :&-: _)   pig 1 = x :&-: unEveryPig pig
    replaceChild (_ :||-: x)  pig 0 = unEveryPig pig :||-: x
    replaceChild (x :||-: _)  pig 1 = x :||-: unEveryPig pig
    replaceChild (_ :->-: x)  pig 0 = unEveryPig pig :->-: x
    replaceChild (x :->-: _)  pig 1 = x :->-: unEveryPig pig
    replaceChild (_ :<->-: x) pig 0 = unEveryPig pig :<->-: x
    replaceChild (x :<->-: _) pig 1 = x :<->-: unEveryPig pig
    replaceChild (_ :+: x)    pig 0 = unEveryPig pig :+: x
    replaceChild (x :+: _)    pig 1 = x :+: unEveryPig pig
    replaceChild (_ :-: x)    pig 0 = unEveryPig pig :-: x
    replaceChild (x :-: _)    pig 1 = x :-: unEveryPig pig
    replaceChild (_ :|-: x)   pig 0 = unEveryPig pig :|-: x
    replaceChild (x :|-: _)   pig 1 = x :|-: unEveryPig pig
    replaceChild (SeqNeg _)   pig _ = SeqNeg $ unEveryPig pig
    replaceChild (SS _ )      pig _ = SS $ unEveryPig pig 
    replaceChild (SA _ )      pig _ = SA $ unEveryPig pig

instance ParsableLex (Form Bool) PurePropLexicon where
        langParser = purePropFormulaParser standardLetters

propSeqParser = seqFormulaParser :: Parsec String u (PropSequentCalc Sequent)

extendedPropSeqParser = parseSeqOver (purePropFormulaParser extendedLetters)

-------------------------
--  1. Standard Rules  --
-------------------------
--Rules found in many systems of propositional logic

modusPonens = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
              , GammaV 2 :|-: SS (SeqPhi 1)
              ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)

modusTollens = [ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
               , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
               ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)

axiom = [] ∴ SA (SeqPhi 1) :|-: SS (SeqPhi 1)

identityRule = [ GammaV 1 :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 1)

doubleNegationElimination = [ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 1) 

doubleNegationIntroduction = [ GammaV 1 :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqNeg $ SeqNeg $ SeqPhi 1) 

adjunction = [ GammaV 1  :|-: SS (SeqPhi 1) 
             , GammaV 2  :|-: SS (SeqPhi 2)
             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1 :&-: SeqPhi 2)

conditionalToBiconditional = [ GammaV 1  :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
                             , GammaV 2  :|-: SS (SeqPhi 2 :->-: SeqPhi 1) 
                             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)

---------------------------
--  1.1 Variation Rules  --
---------------------------
-- Rules with several variations

modusTollendoPonensVariations = [
                [ GammaV 1  :|-: SS (SeqNeg $ SeqPhi 1) 
                , GammaV 2  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            , 
                [ GammaV 1  :|-: SS (SeqNeg $ SeqPhi 1) 
                , GammaV 2  :|-: SS (SeqPhi 2 :||-: SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ]

constructiveReductioVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,

                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,

                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqNeg $ SeqPhi 1)
            ]

nonConstructiveReductioVariations = [
                [ GammaV 1 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ,

                [ GammaV 1 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqPhi 2) 
                , GammaV 2 :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ,

                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2 :+: SA (SeqNeg $ SeqPhi 1) :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 2) 
                , GammaV 2  :|-: SS (SeqNeg $ SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( SeqPhi 1)
            ]

conditionalProofVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2) 
                ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2) 
            ,   [ GammaV 1 :|-: SS (SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
            ]

simplificationVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :&-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1 :&-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 2)
            ]

additionVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :||-: SeqPhi 1)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
            ]

biconditionalToConditionalVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 2 :->-: SeqPhi 1)
            , 
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2) ] ∴ GammaV 1 :|-: SS (SeqPhi 1 :->-: SeqPhi 2)
            ]

proofByCasesVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 3)
                , GammaV 3 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ,   
                [ GammaV 1  :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 3)
                , GammaV 3 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ,   
                [ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 3)
                , GammaV 3 :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            , 
                [ GammaV 1 :|-: SS (SeqPhi 1 :||-: SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 3)
                , GammaV 3 :|-: SS (SeqPhi 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (SeqPhi 3)
            ]

biconditionalProofVariations = [
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ,
                [ GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :+: SA (SeqPhi 2) :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ,
                [ GammaV 1 :+: SA (SeqPhi 1) :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            , 
                [ GammaV 1 :|-: SS (SeqPhi 2)
                , GammaV 2 :|-: SS (SeqPhi 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2 :<->-: SeqPhi 1)
            ]

biconditionalPonensVariations = [
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)
                , GammaV 2  :|-: SS (SeqPhi 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 2)
            ,
                [ GammaV 1  :|-: SS (SeqPhi 1 :<->-: SeqPhi 2)
                , GammaV 2  :|-: SS (SeqPhi 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (SeqPhi 1)
            ]


--------------------------------------------------------
--  2. System 1
--------------------------------------------------------
--A system for propositional logic resembling the proof system from Kalish
--and Montegue's LOGIC, with derived rules

data DerivedRule = DerivedRule { conclusion :: PureForm, premises :: [PureForm]}
               deriving (Show, Eq)

data PropLogic = MP | MT  | DNE | DNI | DD   | AX 
                    | CP1 | CP2 | ID1 | ID2  | ID3  | ID4 
                    | ADJ | S1  | S2  | ADD1 | ADD2 | MTP1 | MTP2 | BC1 | BC2 | CB  
                    | DER DerivedRule
               deriving (Show, Eq)

instance Inference PropLogic PurePropLexicon where
    ruleOf MP        = modusPonens
    ruleOf MT        = modusTollens
    ruleOf AX        = axiom
    ruleOf ID1       = constructiveReductioVariations !! 0
    ruleOf ID2       = constructiveReductioVariations !! 1
    ruleOf ID3       = constructiveReductioVariations !! 2
    ruleOf ID4       = constructiveReductioVariations !! 3
    ruleOf DD        = identityRule
    ruleOf DNE       = doubleNegationElimination
    ruleOf DNI       = doubleNegationIntroduction
    ruleOf CP1       = constructiveReductioVariations !! 0
    ruleOf CP2       = constructiveReductioVariations !! 1
    ruleOf ADJ       = adjunction
    ruleOf S1        = simplificationVariations !! 0
    ruleOf S2        = simplificationVariations !! 1
    ruleOf MTP1      =  modusTollendoPonensVariations !! 0
    ruleOf MTP2      =  modusTollendoPonensVariations !! 1
    ruleOf BC1       = biconditionalToConditionalVariations !! 0
    ruleOf BC2       = biconditionalToConditionalVariations !! 1
    ruleOf CB        = conditionalToBiconditional

    premisesOf (DER r) = zipWith gammafy (premises r) [1..]
        where gammafy p n = GammaV n :|-: SS (liftToSequent p)

    conclusionOf (DER r) = gammas :|-: SS (liftToSequent $ conclusion r)
        where gammas = foldl (:+:) Top (map GammaV [1..length (premises r)])

    indirectInference x
        | x `elem` [DD,CP1,CP2,ID1,ID2,ID3,ID4] = Just PolyProof
        | otherwise = Nothing

parsePropLogic :: Map String DerivedRule -> Parsec String u [PropLogic]
parsePropLogic ders = do r <- choice (map (try . string) ["AS","PR","MP","MTP","MT","DD","DNE","DNI", "DN", "S", "ADJ",  "ADD" , "BC", "CB",  "CD", "ID", "D-"])
                         case r of
                             "AS"   -> return [AX]
                             "PR"   -> return [AX]
                             "MP"   -> return [MP]
                             "MT"   -> return [MT]
                             "DD"   -> return [DD]
                             "DNE"  -> return [DNE]
                             "DNI"  -> return [DNI]
                             "DN"   -> return [DNE,DNI]
                             "CD"   -> return [CP1,CP2]
                             "ID"   -> return [ID1,ID2,ID3,ID4]
                             "ADJ"  -> return [ADJ]
                             "S"    -> return [S1, S2]
                             "ADD"  -> return [ADD1, ADD2]
                             "MTP"  -> return [MTP1, MTP2]
                             "BC"   -> return [BC1, BC2]
                             "CB"   -> return [CB]
                             "D-" -> do rn <- many1 upper
                                        case M.lookup rn ders of
                                            Just r  -> return [DER r]
                                            Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

parsePropProof :: Map String DerivedRule -> String -> [DeductionLine PropLogic PurePropLexicon (Form Bool)]
parsePropProof ders = toDeduction (parsePropLogic ders) (purePropFormulaParser standardLetters)

--------------------------------------------------------
--  3. System 2
--------------------------------------------------------
--A system for propositional logic resembling the proof system SD from
--Bergmann, Moor and Nelson's Logic Book

data LogicBookPropLogic = ConjIntro  
                        | ConjElim1  | ConjElim2
                        | CondIntro1 | CondIntro2
                        | CondElim
                        | NegeIntro1 | NegeIntro2
                        | NegeIntro3 | NegeIntro4
                        | NegeElim1  | NegeElim2
                        | NegeElim3  | NegeElim4
                        | DisjIntro1 | DisjIntro2
                        | DisjElim1  | DisjElim2
                        | DisjElim3  | DisjElim4
                        | BicoIntro1 | BicoIntro2 
                        | BicoIntro3 | BicoIntro4
                        | BicoElim1  | BicoElim2
                        | Reiterate  | LBAX
                        | LBAS
               deriving Eq

instance Show LogicBookPropLogic where
        show ConjIntro  = "∧I"
        show ConjElim1  = "∧E"
        show ConjElim2  = "∧E"
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
        show DisjElim1  = "∨E"
        show DisjElim2  = "∨E"
        show DisjElim3  = "∨E"
        show DisjElim4  = "∨E"
        show DisjIntro1 = "∨I"
        show DisjIntro2 = "∨I"
        show BicoIntro1 = "↔I"
        show BicoIntro2 = "↔I"
        show BicoIntro3 = "↔I"
        show BicoIntro4 = "↔I"
        show BicoElim1  = "↔E"
        show BicoElim2  = "↔E"
        show Reiterate  = "R"
        show LBAX       = "PR"
        show LBAS       = "AS"

instance Inference LogicBookPropLogic PurePropLexicon where
    ruleOf Reiterate  = identityRule
    ruleOf CondElim   = modusPonens
    ruleOf CondIntro1 = conditionalProofVariations !! 0 
    ruleOf CondIntro2 = conditionalProofVariations !! 1
    ruleOf ConjIntro  = adjunction
    ruleOf NegeIntro1 = constructiveReductioVariations !! 0
    ruleOf NegeIntro2 = constructiveReductioVariations !! 1
    ruleOf NegeIntro3 = constructiveReductioVariations !! 2
    ruleOf NegeIntro4 = constructiveReductioVariations !! 3
    ruleOf NegeElim1  = nonConstructiveReductioVariations !! 0
    ruleOf NegeElim2  = nonConstructiveReductioVariations !! 1
    ruleOf NegeElim3  = nonConstructiveReductioVariations !! 2
    ruleOf NegeElim4  = nonConstructiveReductioVariations !! 4
    ruleOf DisjIntro1 = additionVariations !! 0
    ruleOf DisjIntro2 = additionVariations !! 1
    ruleOf DisjElim1  = proofByCasesVariations !! 0
    ruleOf DisjElim2  = proofByCasesVariations !! 1
    ruleOf DisjElim3  = proofByCasesVariations !! 2
    ruleOf DisjElim4  = proofByCasesVariations !! 3
    ruleOf ConjElim1  = simplificationVariations !! 0
    ruleOf ConjElim2  = simplificationVariations !! 1
    ruleOf BicoIntro1 = biconditionalProofVariations !! 0
    ruleOf BicoIntro2 = biconditionalProofVariations !! 1
    ruleOf BicoIntro3 = biconditionalProofVariations !! 2
    ruleOf BicoIntro4 = biconditionalProofVariations !! 3
    ruleOf LBAX       = axiom
    ruleOf LBAS       = axiom
    ruleOf BicoElim1  = biconditionalPonensVariations !! 0
    ruleOf BicoElim2  = biconditionalPonensVariations !! 1

    indirectInference x
        | x `elem` [CondIntro1,CondIntro2, BicoIntro1, BicoIntro2
                   , BicoIntro3, BicoIntro4 , DisjElim1, DisjElim2
                   , DisjElim3, DisjElim4 ] = Just PolyProof
        | x `elem` [ NegeIntro1, NegeIntro2 , NegeIntro3, NegeIntro4
                   , NegeElim1, NegeElim2, NegeElim3, NegeElim4
                   ] = Just DoubleProof
        | otherwise = Nothing

    isAssumption LBAS = True
    isAssumption _ = False

parseFitchPropLogic :: Map String DerivedRule -> Parsec String u [LogicBookPropLogic]
parseFitchPropLogic ders = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I","→E","CE","->E", "→E"
                                                              ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I" 
                                                              , "BE", "<->E", "↔E", "R"])
                              case r of
                                  "AS"   -> return [LBAS]
                                  "PR"   -> return [LBAX]
                                  "&I"   -> return [ConjIntro]
                                  "&E"   -> return [ConjElim1, ConjElim2]
                                  "/\\I" -> return [ConjIntro]
                                  "/\\E" -> return [ConjElim1, ConjElim2]
                                  "∧I"   -> return [ConjIntro]
                                  "∧E"   -> return [ConjElim1, ConjElim2]
                                  "CI"   -> return [CondIntro1,CondIntro2]
                                  "CE"   -> return [CondElim]
                                  "->I"  -> return [CondIntro1,CondIntro2]
                                  "->E"  -> return [CondElim]
                                  "→I"   -> return [CondIntro1,CondIntro2]
                                  "→E"   -> return [CondElim]
                                  "~I"   -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                                  "~E"   -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                                  "¬I"   -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                                  "¬E"   -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                                  "-I"   -> return [NegeIntro1, NegeIntro2, NegeIntro3, NegeIntro4]
                                  "-E"   -> return [NegeElim1, NegeElim2, NegeElim3, NegeElim4]
                                  "vI"   -> return [DisjIntro1, DisjIntro2]
                                  "vE"   -> return [DisjElim1, DisjElim2,DisjElim3, DisjElim4]
                                  "\\/I" -> return [DisjIntro1, DisjIntro2]
                                  "\\/E" -> return [DisjElim1, DisjElim2,DisjElim3, DisjElim4]
                                  "BI"   -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                  "BE"   -> return [BicoElim1, BicoElim2]
                                  "<->I" -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                  "<->E" -> return [BicoElim1, BicoElim2]
                                  "↔I"   -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                  "↔E"   -> return [BicoElim1, BicoElim2]
                                  "R"    -> return [Reiterate]

parseFitchPropProof :: Map String DerivedRule -> String -> [DeductionLine LogicBookPropLogic PurePropLexicon (Form Bool)]
parseFitchPropProof ders = toDeductionBE (parseFitchPropLogic ders) (purePropFormulaParser extendedLetters)

-------------------
--  4. System 3  --
-------------------
--A system for propositional logic resembling the proof system SL from PD
--Magnus' forallx book

data ForallxRules = ReiterateX  | ConjIntroX
                  | ConjElim1X  | ConjElim2X
                  | DisjIntro1X | DisjIntro2X
                  | DisjElim1X  | DisjElem2X
                  | CondIntro1X | CondIntro2X
                  | CondElimX
                  | BicoIntro1X | BicoIntro2X
                  | BicoIntro3X | BicoIntro4X
                  | BicoElim1X  | BicoElim2X
                  | NegeIntro1X | NegeIntro2X
                  | NegeIntro3X | NegeIntro4X
                  | NegeElim1X  | NegeElim2X
                  | NegeElim3X  | NegeElim4X
                  | ForXAssump  | ForXPrem
                  deriving (Show, Eq)
                  --skipping derived rules for now

instance Inference ForallxRules where
        ruleOf ReiterateX = identityRule
        ruleOf ConjIntro = adjunction
        ruleOf ConjElim1X = simplificationVariations !! 0
        ruleOf ConjElim2X = simplificationVariations !! 1
        ruleOf DisjIntro1X = additionVariations !! 0
        ruleOf DisjIntro2X = additionVariations !! 1 
        ruleOf DisjElim1X = modusTollendoPonensVariations !! 0
        ruleOf DisjElim2X = modusTollendoPonensVariations !! 1
        ruleOf CondIntro1 = conditionalProofVariations !! 0
        ruleOf CondIntro2X = conditionalProofVariations !! 1
        ruleOf CondElimX = modusPonens
        ruleOf BicoIntro1X = biconditionalProofVariations !! 0
        ruleOf BicoIntro2X = biconditionalProofVariations !! 1
        ruleOf BicoIntro3X = biconditionalProofVariations !! 2
        ruleOf BicoIntro4X = biconditionalProofVariations !! 3
        ruleOf BicoElim1X = biconditionalPonensVariations !! 0
        ruleOf BicoElim2X = biconditionalPonensVariations !! 1
        ruleOf NegeIntro1 = constructiveReductioVariations !! 0
        ruleOf NegeIntro2 = constructiveReductioVariations !! 1
        ruleOf NegeIntro3 = constructiveReductioVariations !! 2
        ruleOf NegeIntro4 = constructiveReductioVariations !! 3
        ruleOf NegeElim1 = nonConstructiveReductioVariations !! 0
        ruleOf NegeElim2 = nonConstructiveReductioVariations !! 1
        ruleOf NegeElim3 = nonConstructiveReductioVariations !! 2
        ruleOf NegeElim4 = nonConstructiveReductioVariations !! 3
        ruleOf ForXAssump = axiom
        ruleOf ForXPrem  = axiom

        indirectInference x
            | x `elem` [CondIntro1X,CondIntro2X, BicoIntro1X, BicoIntro2X
                       , BicoIntro3X, BicoIntro4X ] = Just PolyProof
            | x `elem` [ NegeIntro1X, NegeIntro2X , NegeIntro3X, NegeIntro4X
                       , NegeElim1X, NegeElim2X, NegeElim3X , NegeElim4X
                       ] = Just DoubleProof
            | otherwise = Nothing

        isAssumption ForXAssump = True
        isAssumption _ = False


parseForallXPropLogic :: Map String DerivedRule -> Parsec String u [LogicBookPropLogic]
parseForallXPropLogic ders = do r <- choice (map (try . string) ["AS","PR","&I","/\\I", "∧I","&E","/\\E","∧E","CI","->I","→I","→E","CE","->E", "→E"
                                                              ,"~I","-I", "¬I","~E","-E","¬E" ,"vI","\\/I","∨I", "vE","\\/E", "∨E","BI","<->I", "↔I" 
                                                              , "BE", "<->E", "↔E", "R"])
                                case r of
                                    "AS"   -> return [ForXAssump]
                                    "PR"   -> return [ForXPrem]
                                    "&I"   -> return [ConjIntroX]
                                    "&E"   -> return [ConjElim1X, ConjElim2X]
                                    "/\\I" -> return [ConjIntroX]
                                    "/\\E" -> return [ConjElim1X, ConjElim2X]
                                    "∧I"   -> return [ConjIntroX]
                                    "∧E"   -> return [ConjElim1X, ConjElim2X]
                                    "CI"   -> return [CondIntro1X,CondIntro2X]
                                    "CE"   -> return [CondElimX]
                                    "->I"  -> return [CondIntro1X,CondIntro2X]
                                    "->E"  -> return [CondElimX]
                                    "→I"   -> return [CondIntro1X,CondIntro2X]
                                    "→E"   -> return [CondElimX]
                                    "~I"   -> return [NegeIntro1X, NegeIntro2X, NegeIntro3X, NegeIntro4X]
                                    "~E"   -> return [NegeElim1X, NegeElim2X, NegeElim3X, NegeElim4X]
                                    "¬I"   -> return [NegeIntro1X, NegeIntro2X, NegeIntro3X, NegeIntro4X]
                                    "¬E"   -> return [NegeElim1X, NegeElim2X, NegeElim3X, NegeElim4X]
                                    "-I"   -> return [NegeIntro1X, NegeIntro2X, NegeIntro3X, NegeIntro4X]
                                    "-E"   -> return [NegeElim1X, NegeElim2X, NegeElim3X, NegeElim4X]
                                    "vI"   -> return [DisjIntro1X, DisjIntro2X]
                                    "vE"   -> return [DisjElim1X, DisjElim2X]
                                    "\\/I" -> return [DisjIntro1X, DisjIntro2X]
                                    "\\/E" -> return [DisjElim1X, DisjElim2X]
                                    "BI"   -> return [BicoIntro1X, BicoIntro2X, BicoIntro3X, BicoIntro4X]
                                    "BE"   -> return [BicoElim1, BicoElim2]
                                    "<->I" -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                    "<->E" -> return [BicoElim1, BicoElim2]
                                    "↔I"   -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                    "↔E"   -> return [BicoElim1, BicoElim2]
                                    "R"    -> return [Reiterate]
