{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.OpenLogic
    ( parseOLPPropNK, olpPropLKCalc, olpPropLJCalc, olpPropNKCalc, OLPPropNK()
    ) where

import Text.Parsec
import Data.List
import Data.Tree
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Types (Form, FirstOrderLex(..))
import Carnap.Core.Unification.Unification
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Gentzen
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.Util
import Control.Lens
import Carnap.Languages.Util.LanguageClasses

data OLPPropNK = AndI     | AndEL       | AndER
               | OrIL     | OrIR        | OrE Int | OrELVac Int 
               | OrERVac Int | OrEVac (Maybe Int) 
               | IfI Int  | IfIVac (Maybe Int)  | IfE
               | NegI Int | NegIVac (Maybe Int) | NegE  | FalsumE
               | As Int   | IP Int | IPVac (Maybe Int)
               | Pr 
    deriving Eq

instance Show OLPPropNK where
    show AndI = "&I"
    show AndEL = "&E"
    show AndER = "&E"
    show OrIL = "∨I"
    show OrIR = "∨I"
    show (OrE n) = "∨E (" ++ show n ++ ")"
    show (OrELVac m) = "∨E  (" ++ show m ++ ")"
    show (OrERVac n ) = "∨E (" ++ show n ++ ")"
    show (OrEVac (Just m)) = "∨E (" ++ show m ++ ")"
    show (OrEVac Nothing) = "∨E"
    show (IfI n) = "⊃I (" ++ show n ++ ")"
    show (IfIVac (Just n)) = "⊃I (" ++ show n ++ ")"
    show (IfIVac Nothing) = "⊃I"
    show IfE = "⊃E"
    show (NegI n) = "¬I (" ++ show n ++ ")" 
    show (NegIVac (Just n)) = "¬I (" ++ show n ++ ")" 
    show (NegIVac Nothing) = "¬I"
    show (IP n) = "IP (" ++ show n ++ ")" 
    show (IPVac (Just n)) = "IP (" ++ show n ++ ")" 
    show (IPVac Nothing) = "IP"
    show NegE = "¬E"
    show FalsumE = "¬E"
    show (As n) = "(" ++ show n ++ ")"
    show Pr = "Pr"

parseOLPPropNK :: Parsec String u [OLPPropNK]
parseOLPPropNK = parseProp <* spaces <* eof
    where parseProp = choice . map try $
                        [ stringOpts ["&Intro","/\\Intro", "&I","/\\I"] >> return [AndI]
                        , stringOpts ["&Elim","/\\Elim", "&E","/\\E"] >> return [AndER, AndEL]
                        , stringOpts  ["∨Intro","\\/Intro","∨I","\\/I"] >> return [OrIL, OrIR]
                        , stringOpts ["⊃Elim",">Elim", "->Elim", "⊃Elim",">E", "->E"] >> return [IfE]
                        , stringOpts ["¬Elim","-Elim", "~Elim", "¬E","-E", "~E"] >> return [NegE]
                        , stringOpts ["X"] >> return [FalsumE]
                        , getLabel
                            >>= \s -> return [As (read s :: Int)]
                        , (stringOpts ["->Intro", ">Intro","⊃Intro", "->I", ">I","⊃I"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [IfI val, IfIVac (Just val)])
                        , stringOpts ["->Intro", ">Intro","⊃Intro", "->I", ">I","⊃I"] >> return [IfIVac Nothing]
                        , (stringOpts ["¬Intro", "-Intro", "~Intro", "¬I", "-I", "~I"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [NegI val, NegIVac (Just val)])
                        , stringOpts ["¬Intro", "-Intro", "~Intro", "¬I", "-I", "~I"] >> return [NegIVac Nothing]
                        , (stringOpts ["IP"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [IP val, IPVac (Just val)])
                        , stringOpts ["IP"] >> return [IPVac Nothing]
                        , (stringOpts ["∨Elim","\\/Elim", "∨E","\\/E"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [OrE val, OrELVac val, OrERVac val , OrEVac (Just val)])
                        , stringOpts ["∨Elim","\\/Elim", "∨E","\\/E"] >> return [OrEVac Nothing]
                        , eof >> return [Pr]
                        ]
          stringOpts = (choice . map (try . string))
          getLabel = (char '(' *> many1 digit <* char ')') <|> many1 digit
instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference OLPPropNK lex (Form Bool) where
         coreRuleOf AndI = adjunction
         coreRuleOf AndEL = simplificationVariations !! 0
         coreRuleOf AndER = simplificationVariations !! 1
         coreRuleOf OrIL = additionVariations !! 0
         coreRuleOf OrIR = additionVariations !! 1
         coreRuleOf (OrE _) = proofByCasesVariations !! 0
         coreRuleOf (OrELVac _) = proofByCasesVariations !! 1
         coreRuleOf (OrERVac _) = proofByCasesVariations !! 2
         coreRuleOf (OrEVac _) = proofByCasesVariations !! 3
         coreRuleOf (IfI _) = conditionalProofVariations !! 0
         coreRuleOf (IfIVac _) = conditionalProofVariations !! 1
         coreRuleOf IfE = modusPonens
         coreRuleOf (NegI _) = constructiveFalsumReductioVariations !! 0
         coreRuleOf (NegIVac _) = constructiveFalsumReductioVariations !! 1
         coreRuleOf NegE = falsumIntroduction
         coreRuleOf FalsumE = falsumElimination
         coreRuleOf (As _) = axiom
         coreRuleOf Pr = axiom
         coreRuleOf (IP _) = nonConstructiveFalsumReductioVariations !! 0 
         coreRuleOf (IPVac _) = nonConstructiveFalsumReductioVariations !! 1

instance Inference OLPPropNK PurePropLexicon (Form Bool) where
        ruleOf x = coreRuleOf x

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , PrismSchematicProp lex Bool
         , PrismBooleanConnLex lex Bool
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , Eq (ClassicalSequentOver lex (Succedent (Form Bool)))
         , Eq r
         , ReLex lex
         , AssumptionNumbers r
         ) => StructuralInference OLPPropNK lex (ProofTree r lex (Form Bool)) where
    structuralRestriction pt _ (IfI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump)
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (IfIVac (Just n)) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (NegI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump )
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (NegIVac (Just n)) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (IP n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump )
        where assump = SS . liftToSequent $ lneg (phin 1)
    structuralRestriction pt _ (IPVac (Just n)) = Just (usesAssumption n pt assump)
        where assump = SS . liftToSequent $ lneg (phin 1)
    structuralRestriction pt _ (OrE n) = Just $ usesAssumptions n pt [assump 1, assump 2]
                                     `andFurtherRestriction` exhaustsAssumptions n pt (assump 1) 
                                     `andFurtherRestriction` exhaustsAssumptions n pt (assump 2)
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrERVac n) = Just $ usesAssumptions n pt [assump 1, assump 2] 
                                                `andFurtherRestriction` exhaustsAssumptions n pt (assump 1)
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrELVac n) = Just $ usesAssumptions n pt [assump 1, assump 2]
                                                    `andFurtherRestriction` exhaustsAssumptions n pt (assump 2)
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrEVac (Just n)) = Just $ usesAssumptions n pt [assump 1, assump 2] 
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ r = Nothing

instance StructuralOverride OLPPropNK (ProofTree r PurePropLexicon (Form Bool))

instance AssumptionNumbers OLPPropNK where
        introducesAssumptions (As n) = [n]
        introducesAssumptions Pr = [-1] 
        --XXX: premises introduce assumptions that can't be discharged.
        introducesAssumptions _ = []

        dischargesAssumptions (IfI n) = [n]
        dischargesAssumptions (IfIVac (Just n)) = [n]
        dischargesAssumptions (NegI n) = [n]
        dischargesAssumptions (NegIVac (Just n)) = [n]
        dischargesAssumptions (IP n) = [n]
        dischargesAssumptions (IPVac (Just n)) = [n]
        dischargesAssumptions (OrE n) = [n]
        dischargesAssumptions (OrELVac m) = [m]
        dischargesAssumptions (OrERVac n ) = [n]
        dischargesAssumptions (OrEVac (Just n)) = [n]
        dischargesAssumptions _ = []

olpPropNKCalc :: TableauCalc PurePropLexicon (Form Bool) OLPPropNK
olpPropNKCalc = mkTBCalc
    { tbParseForm = purePropFormulaParser thomasBolducZach2019Opts
    , tbParseRule = parseOLPPropNK
    , tbNotation = dropOuterParens
    }

olpPropLKCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLK
olpPropLKCalc = gentzenPropLKCalc 
    { tbParseForm = purePropFormulaParser thomasBolducZach2019Opts 
    , tbNotation = filter (/= '⊤') . dropOuterParens
    }

olpPropLJCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLJ
olpPropLJCalc = gentzenPropLJCalc 
    { tbParseForm = purePropFormulaParser thomasBolducZach2019Opts 
    , tbNotation = filter (/= '⊤') . dropOuterParens
    }
