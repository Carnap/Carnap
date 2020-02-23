{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.OpenLogic
    ( parseOLPPropNK, olpPropNKCalc, OLPPropNK()
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
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.Util
import Control.Lens
import Carnap.Languages.Util.LanguageClasses

data OLPPropNK = AndI     | AndEL       | AndER
               | OrIL     | OrIR        | OrE Int Int | OrELVac (Maybe Int) Int 
               | OrERVac Int (Maybe Int)| OrEVac (Maybe Int) (Maybe Int)
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
    show (OrE n m) = "∨E (" ++ show n ++ ") (" ++ show m ++ ")"
    show (OrELVac (Just n) m) = "∨E (" ++ show n ++ ") (" ++ show m ++ ")"
    show (OrELVac Nothing m) = "∨E (" ++ show m ++ ")"
    show (OrERVac n (Just m)) = "∨E (" ++ show n ++ ") (" ++ show m ++ ")"
    show (OrERVac n Nothing) = "∨E (" ++ show n ++ ")"
    show (OrEVac (Just n) (Just m)) = "∨E (" ++ show n ++ ") (" ++ show m ++ ")"
    show (OrEVac Nothing (Just m)) = "∨E (" ++ show m ++ ")"
    show (OrEVac (Just n) Nothing) = "∨E (" ++ show n ++ ")"
    show (OrEVac Nothing Nothing) = "∨E"
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
parseOLPPropNK = choice . map try $
                        [ stringOpts ["&Intro","/\\Intro", "&I","/\\I"] >> return [AndI]
                        , stringOpts ["&Elim","/\\Elim", "&E","/\\E"] >> return [AndER, AndEL]
                        , stringOpts  ["∨Intro","\\/Intro","∨I","\\/I"] >> return [OrIL, OrIR]
                        , stringOpts ["⊃Elim",">Elim", "->Elim", "⊃Elim",">E", "->E"] >> return [IfE]
                        , stringOpts ["¬Elim","-Elim", "¬E","-E"] >> return [NegE]
                        , stringOpts ["X"] >> return [FalsumE]
                        , char '(' *> many1 digit <* char ')' 
                            >>= \s -> return [As (read s :: Int)]
                        , (stringOpts ["->Intro", ">Intro","⊃Intro", "->I", ">I","⊃I"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [IfI val, IfIVac (Just val)])
                        , stringOpts ["->Intro", ">Intro","⊃Intro", "->I", ">I","⊃I"] >> return [IfIVac Nothing]
                        , (stringOpts ["¬Intro", "-Intro", "¬I", "-I"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [NegI val, NegIVac (Just val)])
                        , stringOpts ["¬Intro", "-Intro", "¬I", "-I"] >> return [NegIVac Nothing]
                        , (stringOpts ["IP"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [IP val, IPVac (Just val)])
                        , stringOpts ["IP"] >> return [IPVac Nothing]
                        , (,) <$> (stringOpts ["∨Elim","\\/Elim", "∨E","\\/E"] *> spaces *> char '(' *> many1 digit <* char ')')
                              <*> (spaces *> char '(' *> many1 digit <* char ')')
                            >>= \(s1,s2) -> return $ let val1 = read s1 :: Int
                                                         val2 = read s2 :: Int
                                                     in [OrE val1 val2, OrELVac (Just val1) val2, OrERVac val1 (Just val2), OrEVac (Just val1) (Just val2)]
                        , (stringOpts ["∨Elim","\\/Elim", "∨E","\\/E"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [OrELVac Nothing val, OrERVac val Nothing, OrEVac (Just val) Nothing])
                        , stringOpts ["∨Elim","\\/Elim", "∨E","\\/E"] >> return [OrEVac Nothing Nothing]
                        , eof >> return [Pr]
                        ]
    where stringOpts = choice . map (try . string)

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
         coreRuleOf (OrE n m) = proofByCasesVariations !! 0
         coreRuleOf (OrELVac _ _) = proofByCasesVariations !! 1
         coreRuleOf (OrERVac _ _) = proofByCasesVariations !! 2
         coreRuleOf (OrEVac _ _) = proofByCasesVariations !! 3
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

instance AssumptionNumbers r => StructuralInference OLPPropNK PurePropLexicon (ProofTree r PurePropLexicon (Form Bool)) where
    structuralRestriction pt _ (As n) = Just noReps
        where noReps _ | allEq (leavesLabeled n pt) = Nothing
                       | otherwise = Just "Distinct assumptions are getting the same index"
              allEq ((Node x _):xs) = all (\(Node pl _) -> content pl == content x) xs
    structuralRestriction pt _ (IfI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump)
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (IfIVac (Just n)) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (NegI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump )
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (NegIVac (Just n)) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (IP n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump )
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (IPVac (Just n)) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (OrE n m) = Just $ \sub -> doubleAssumption 1 2 sub >> doubleAssumption 2 1 sub
        where doubleAssumption j k = usesAssumption n pt (assump j)      `andFurtherRestriction` 
                                     usesAssumption m pt (assump k)      `andFurtherRestriction` 
                                     exhaustsAssumptions n pt (assump j) `andFurtherRestriction` 
                                     exhaustsAssumptions m pt (assump k)
              assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrERVac n (Just m)) = Just (usesAssumption n pt (assump 1) 
                                                `andFurtherRestriction` usesAssumption m pt (assump 2)
                                                `andFurtherRestriction` exhaustsAssumptions n pt (assump 1))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrERVac n Nothing) = Just (usesAssumption n pt (assump 1) 
                                                `andFurtherRestriction` exhaustsAssumptions n pt (assump 1))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrELVac (Just n) m) = Just (usesAssumption n pt (assump 1) 
                                                `andFurtherRestriction` usesAssumption m pt (assump 2)
                                                `andFurtherRestriction` exhaustsAssumptions m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrELVac Nothing m) = Just (usesAssumption m pt (assump 2)
                                                `andFurtherRestriction` exhaustsAssumptions m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrEVac (Just n) (Just m)) = Just (usesAssumption n pt (assump 1) 
                                                  `andFurtherRestriction` usesAssumption m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrEVac Nothing (Just m)) = Just (usesAssumption m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrEVac (Just n) Nothing) = Just (usesAssumption n pt (assump 1))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ r = Nothing

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
        dischargesAssumptions (OrE n m) = [n,m]
        dischargesAssumptions (OrELVac (Just n) m) = [n,m]
        dischargesAssumptions (OrELVac Nothing m) = [m]
        dischargesAssumptions (OrERVac n (Just m)) = [n,m]
        dischargesAssumptions (OrERVac n Nothing) = [n]
        dischargesAssumptions (OrEVac (Just n) (Just m)) = [n,m]
        dischargesAssumptions (OrEVac (Just n) Nothing) = [n]
        dischargesAssumptions (OrEVac Nothing (Just m)) = [m]
        dischargesAssumptions _ = []

olpPropNKCalc :: TableauCalc PurePropLexicon (Form Bool) OLPPropNK
olpPropNKCalc = TableauCalc 
    { tbParseForm = purePropFormulaParser thomasBolducZachOpts
    , tbParseRule = parseOLPPropNK
    }
