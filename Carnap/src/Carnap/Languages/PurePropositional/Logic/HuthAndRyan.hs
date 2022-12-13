{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.HuthAndRyan
    (parseHuthAndRyanPropNK, huthAndRyanPropNKCalc, HuthAndRyanPropNK()) where

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



data HuthAndRyanPropNK = AndI     | AndEL       | AndER
                   | OrIL     | OrIR        | OrE Int Int | OrELVac (Maybe Int) Int 
                   | OrERVac Int (Maybe Int)| OrEVac (Maybe Int) (Maybe Int)
                   | IfI Int  | IfIVac (Maybe Int)  | IfE
                   | NegI Int | NegIVac (Maybe Int) | NegE  | FalsumE
                   | DNE | PBC Int | PBCVac (Maybe Int) | LEM | MT | DNI
                   | As Int
                   | Pr
    deriving Eq



instance Show HuthAndRyanPropNK where
    show AndI = "&I"
    show AndEL = "&E1"
    show AndER = "&E2"
    show OrIL = "∨I1"
    show OrIR = "∨I2"
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
    show NegE = "¬E"
    show FalsumE = "⊥E"
    show DNE = "¬¬E"
    show (PBC n) = "PBC (" ++ show n ++ ")"
    show (PBCVac (Just n)) = "PBC (" ++ show n ++ ")"
    show (PBCVac Nothing) = "PBC"
    show LEM = "LEM"
    show MT = "MT"
    show DNI = "¬¬I"
    show (As n) = "(" ++ show n ++ ")"
    show Pr = "Pr"


parseHuthAndRyanPropNK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [HuthAndRyanPropNK]
parseHuthAndRyanPropNK rtc = choice . map try $
                        [ stringOpts ["&I","/\\I"] >> return [AndI]
                        , stringOpts ["&E1","/\\E1"] >> return [AndEL]
                        , stringOpts ["&E2","/\\E2"] >> return [AndER]
                        , stringOpts  ["∨I1","\\/I1"] >> return [OrIL]
                        , stringOpts  ["∨I2","\\/I2"] >> return [OrIR]
                        , stringOpts ["⊃E",">E", "->E"] >> return [IfE]
                        , stringOpts ["¬E","-E"] >> return [NegE]
                        , stringOpts ["⊥E","XE"] >> return [FalsumE]
                        , stringOpts ["¬¬E","--E"] >> return [DNE]
                        , stringOpts ["¬¬I","--I"] >> return [DNI]
                        , string "LEM" >> return [LEM]
                        , string "MT" >> return [MT]
                        , char '(' *> many1 digit <* char ')' 
                            >>= \s -> return [As (read s :: Int)]
                        , (stringOpts ["->I", ">I","⊃I"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [IfI val, IfIVac (Just val)])
                        , stringOpts ["->I", ">I","⊃I"] >> return [IfIVac Nothing]
                        , (stringOpts ["¬I", "-I"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [NegI val, NegIVac (Just val)])
                        , stringOpts ["¬I", "-I"] >> return [NegIVac Nothing]
                        , (,) <$> (stringOpts ["∨E","\\/E"] *> spaces *> char '(' *> many1 digit <* char ')')
                              <*> (spaces *> char '(' *> many1 digit <* char ')')
                            >>= \(s1,s2) -> return $ let val1 = read s1 :: Int
                                                         val2 = read s2 :: Int
                                                     in [OrE val1 val2, OrELVac (Just val1) val2, OrERVac val1 (Just val2), OrEVac (Just val1) (Just val2)]
                        , (stringOpts ["∨E","\\/E"] *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [OrELVac Nothing val, OrERVac val Nothing, OrEVac (Just val) Nothing])
                        , stringOpts ["∨E","\\/E"] >> return [OrEVac Nothing Nothing]
                        , (string "PBC" *> spaces *> char '(' *> many1 digit <* char ')') 
                            >>= \s -> return (let val = read s :: Int in [PBC val, PBCVac (Just val)])
                        , string "PBC" >> return [PBCVac Nothing]
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
         ) => CoreInference HuthAndRyanPropNK lex (Form Bool) where
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
         coreRuleOf DNE = doubleNegationElimination
         coreRuleOf DNI = doubleNegationIntroduction
         coreRuleOf (PBC _) = nonConstructiveFalsumReductioVariations !! 0
         coreRuleOf (PBCVac _) = nonConstructiveFalsumReductioVariations !! 1
         coreRuleOf MT = modusTollens
         coreRuleOf LEM = [] ∴ Top :|-: SS (phin 1 .\/. (lneg $ phin 1))
         coreRuleOf (As _) = axiom
         coreRuleOf Pr = axiom


instance Inference HuthAndRyanPropNK PurePropLexicon (Form Bool) where
        ruleOf x = coreRuleOf x

instance (Eq r, AssumptionNumbers r) => StructuralInference HuthAndRyanPropNK PurePropLexicon (ProofTree r PurePropLexicon (Form Bool)) where
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
    structuralRestriction pt _ (PBC n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump )
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (PBCVac (Just n)) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (OrE n m) = Just $ \sub -> doubleAssumption 1 2 sub >> doubleAssumption 2 1 sub
        --the point of the doubleAssumption here is to allow either that
        --n points to phi_1 or to phi_2; because of the way the maybe monad
        --works, if we get a Nothing ("OK") from either test, we say the
        --restriction is respected.
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

instance StructuralOverride HuthAndRyanPropNK (ProofTree r PurePropLexicon (Form Bool))

instance AssumptionNumbers HuthAndRyanPropNK where
        introducesAssumptions (As n) = [n]
        introducesAssumptions Pr = [-1] 
        --XXX: premises introduce assumptions that can't be discharged.
        introducesAssumptions _ = []

        dischargesAssumptions (IfI n) = [n]
        dischargesAssumptions (IfIVac (Just n)) = [n]
        dischargesAssumptions (NegI n) = [n]
        dischargesAssumptions (NegIVac (Just n)) = [n]
        dischargesAssumptions (PBC n) = [n]
        dischargesAssumptions (PBCVac (Just n)) = [n]
        dischargesAssumptions (OrE n m) = [n,m]
        dischargesAssumptions (OrELVac (Just n) m) = [n,m]
        dischargesAssumptions (OrELVac Nothing m) = [m]
        dischargesAssumptions (OrERVac n (Just m)) = [n,m]
        dischargesAssumptions (OrERVac n Nothing) = [n]
        dischargesAssumptions (OrEVac (Just n) (Just m)) = [n,m]
        dischargesAssumptions (OrEVac (Just n) Nothing) = [n]
        dischargesAssumptions (OrEVac Nothing (Just m)) = [m]
        dischargesAssumptions _ = []

huthAndRyanPropNKCalc :: TableauCalc PurePropLexicon (Form Bool) HuthAndRyanPropNK
huthAndRyanPropNKCalc = mkTBCalc
    { tbParseForm = purePropFormulaParser hardegreeOpts
    , tbParseRule = parseHuthAndRyanPropNK
    }
