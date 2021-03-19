{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.OpenLogic
    ( parseOpenLogicPropLK, parseOpenLogicPropNK, olpPropLKCalc, olpPropLJCalc, olpPropNKCalc
    , OpenLogicPropNK(), OpenLogicPropLJ(), OpenLogicPropLK()) where

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

data OpenLogicPropNK = AndI     | AndEL       | AndER
               | OrIL     | OrIR        | OrE Int | OrELVac Int 
               | OrERVac Int | OrEVac (Maybe Int) 
               | IfI Int  | IfIVac (Maybe Int)  | IfE
               | IffI Int | IffIRVac Int | IffILVac Int | IffIVac (Maybe Int) | IffE1 | IffE2
               | NegI Int | NegIVac (Maybe Int) | NegE  | FalsumE
               | As Int   | IP Int | IPVac (Maybe Int)
               | Pr 
    deriving Eq

data OpenLogicPropLK = GentzenPropLK GentzenPropLK | IffR | IffL1 | IffL2 
    deriving Eq

newtype OpenLogicPropLJ = LJ OpenLogicPropLK
    deriving Eq

instance Show OpenLogicPropNK where
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
    show (IffI n) = "↔I (" ++ show n ++ ")"
    show (IffILVac n)  = "↔I (" ++ show n ++ ")"
    show (IffIRVac n) = "↔I (" ++ show n ++ ")"
    show (IffIVac (Just n)) = "↔I (" ++ show n ++ ")"
    show (IffIVac Nothing) = "↔I"
    show IffE1 = "↔E"
    show IffE2 = "↔E"
    show IfE = "⊃E"
    show (NegI n) = "¬I (" ++ show n ++ ")" 
    show (NegIVac (Just n)) = "¬I (" ++ show n ++ ")" 
    show (NegIVac Nothing) = "¬I"
    show (IP n) = "IP (" ++ show n ++ ")" 
    show (IPVac (Just n)) = "IP (" ++ show n ++ ")" 
    show (IPVac Nothing) = "IP"
    show NegE = "¬E"
    show FalsumE = "X"
    show (As n) = "(" ++ show n ++ ")"
    show Pr = "Pr"

instance Show OpenLogicPropLJ where
    show (LJ x) = show x

instance Show OpenLogicPropLK where
        show (GentzenPropLK x) = show x
        show IffR = "↔R"
        show IffL1 = "↔L"
        show IffL2 = "↔L"

parseOpenLogicPropNK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [OpenLogicPropNK]
parseOpenLogicPropNK rtc = parseProp <* spaces <* eof
    where parseProp = choice . map try $
                        [ stringOpts ["&Intro","/\\Intro", "∧Intro", "&I","/\\I", "∧I"] >> return [AndI]
                        , stringOpts ["&Elim","/\\Elim", "∧Elim", "&E","/\\E", "∧E"] >> return [AndER, AndEL]
                        , stringOpts ["∨Intro","\\/Intro","∨I","\\/I"] >> return [OrIL, OrIR]
                        , stringOpts ["⊃Elim",">Elim", "->Elim", "->Elim","⊃E", ">E", "->E",  "→E"] >> return [IfE]
                        , stringOpts ["¬Elim","-Elim", "~Elim", "¬E","-E", "~E"] >> return [NegE]
                        , stringOpts ["X"] >> return [FalsumE]
                        , getLabel
                            >>= \s -> return [As (read s :: Int)]
                        , (stringOpts ["->Intro", ">Intro", "⊃Intro", "→Intro", "->I", ">I","⊃I","→I"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [IfI val, IfIVac (Just val)])
                        , stringOpts ["⊃Intro", ">Intro", "->Intro", "→Intro", "⊃I", ">I", "->I", "→I"] >> return [IfIVac Nothing]
                        , (stringOpts ["¬Intro", "-Intro", "~Intro", "¬I", "-I", "~I"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [NegI val, NegIVac (Just val)])
                        , stringOpts ["¬Intro", "-Intro", "~Intro", "¬I", "-I", "~I"] >> return [NegIVac Nothing]
                        , (stringOpts ["IP"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [IP val, IPVac (Just val)])
                        , stringOpts ["IP"] >> return [IPVac Nothing]
                        , (stringOpts ["∨Elim","\\/Elim", "∨E","\\/E"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [OrE val, OrELVac val, OrERVac val , OrEVac (Just val)])
                        , stringOpts ["∨Elim","\\/Elim", "∨E","\\/E"] >> return [OrEVac Nothing]
                        , (stringOpts ["<->Intro ","<->I", "↔Intro", "↔I"] *> spaces *> getLabel) 
                            >>= \s -> return (let val = read s :: Int in [IffI val, IffILVac val , IffIRVac val, IffIVac (Just val)])
                        , stringOpts ["<->Intro ","<->I", "↔Intro", "↔I"] >> return [IffIVac Nothing]
                        , stringOpts ["<->Elim","<->E", "↔Elim", "↔E"] >> return [IffE1, IffE2]
                        , eof >> return [Pr]
                        ]
          stringOpts = (choice . map (try . string))
          getLabel = (char '(' *> many1 digit <* char ')') <|> many1 digit

parseOpenLogicPropLK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [OpenLogicPropLK]
parseOpenLogicPropLK rtc = try parseGentzen <|> parseIff
    where parseGentzen = map GentzenPropLK <$> parseGentzenPropLK rtc
          parseIff = choice . map try $ [ stringOpts ["<->L", "↔L", "<>L"] >> return [IffL1, IffL2]
                                        , stringOpts ["<->R", "↔R", "<>R"] >> return [IffR]
                                        ]
          stringOpts = (choice . map (try . string))

parseOpenLogicPropLJ :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [OpenLogicPropLJ]
parseOpenLogicPropLJ rtc = map LJ <$> parseOpenLogicPropLK rtc

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference OpenLogicPropNK lex (Form Bool) where
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
         coreRuleOf (IffI _) = biconditionalProofVariations !! 0
         coreRuleOf (IffILVac _) = biconditionalProofVariations !! 1
         coreRuleOf (IffIRVac _) = biconditionalProofVariations !! 2
         coreRuleOf (IffIVac _) = biconditionalProofVariations !! 3
         coreRuleOf IffE1 = biconditionalPonensVariations !! 0
         coreRuleOf IffE2 = biconditionalPonensVariations !! 1
         coreRuleOf (NegI _) = constructiveFalsumReductioVariations !! 0
         coreRuleOf (NegIVac _) = constructiveFalsumReductioVariations !! 1
         coreRuleOf NegE = falsumIntroduction
         coreRuleOf FalsumE = falsumElimination
         coreRuleOf (As _) = axiom
         coreRuleOf Pr = axiom
         coreRuleOf (IP _) = nonConstructiveFalsumReductioVariations !! 0 
         coreRuleOf (IPVac _) = nonConstructiveFalsumReductioVariations !! 1

instance Inference OpenLogicPropNK PurePropLexicon (Form Bool) where
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
         ) => StructuralInference OpenLogicPropNK lex (ProofTree r lex (Form Bool)) where
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
    structuralRestriction pt _ (IffI n) = Just $ usesAssumptions n pt [assump 1, assump 2]
                                     `andFurtherRestriction` exhaustsAssumptions n pt (assump 1) 
                                     `andFurtherRestriction` exhaustsAssumptions n pt (assump 2)
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (IffIRVac n) = Just $ usesAssumptions n pt [assump 1, assump 2] 
                                                `andFurtherRestriction` exhaustsAssumptions n pt (assump 1)
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (IffILVac n) = Just $ usesAssumptions n pt [assump 1, assump 2]
                                                    `andFurtherRestriction` exhaustsAssumptions n pt (assump 2)
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (IffIVac (Just n)) = Just $ usesAssumptions n pt [assump 1, assump 2] 
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ r = Nothing

instance StructuralOverride OpenLogicPropNK (ProofTree r PurePropLexicon (Form Bool))

instance AssumptionNumbers OpenLogicPropNK where
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
        dischargesAssumptions (IffI n) = [n]
        dischargesAssumptions (IffILVac m) = [m]
        dischargesAssumptions (IffIRVac n ) = [n]
        dischargesAssumptions (IffIVac (Just n)) = [n]
        dischargesAssumptions _ = []

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference OpenLogicPropLK lex (Form Bool) where
         corePremisesOf (GentzenPropLK x) = corePremisesOf x
         corePremisesOf IffR = [ SA (phin 1) :+: GammaV 1 :|-: DeltaV 1 :-: SS (phin 2)
                               , SA (phin 2) :+: GammaV 1 :|-: DeltaV 1 :-: SS (phin 1)
                               ]
         corePremisesOf IffL1 = [ SA (phin 2) :+: GammaV 1 :|-: DeltaV 1 
                                , GammaV 1 :|-: DeltaV 1 :-: SS (phin 1) 
                                ]
         corePremisesOf IffL2 = [ SA (phin 1) :+: GammaV 1 :|-: DeltaV 1 
                                , GammaV 1 :|-: DeltaV 1 :-: SS (phin 2) 
                                ]

         coreConclusionOf (GentzenPropLK x) = coreConclusionOf x
         coreConclusionOf IffR = GammaV 1 :|-: DeltaV 1 :-: SS (phin 1 .<=>. phin 2)
         coreConclusionOf IffL1 = SA (phin 1 .<=>. phin 2) :+: GammaV 1 :|-: DeltaV 1 
         coreConclusionOf IffL2 = SA (phin 1 .<=>. phin 2) :+: GammaV 1 :|-: DeltaV 1 

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference OpenLogicPropLJ lex (Form Bool) where
         corePremisesOf (LJ x) = corePremisesOf x

         coreConclusionOf (LJ x) = coreConclusionOf x

         coreRestriction x = Just $ \sub -> monoConsequent (applySub sub $ coreConclusionOf x)
             where monoConsequent :: forall lex . Eq (ClassicalSequentOver lex (Form Bool)) => ClassicalSequentOver lex (Sequent (Form Bool)) -> Maybe String
                   monoConsequent (_:|-:x)= case nub (toListOf concretes x :: [ClassicalSequentOver lex (Form Bool)]) of
                                              _:_:xs -> Just "LJ requires that the right hand side of each sequent contain at most one formula"
                                              _ -> Nothing

instance SpecifiedUnificationType OpenLogicPropLJ

instance SpecifiedUnificationType OpenLogicPropLK

olpPropNKCalc :: TableauCalc PurePropLexicon (Form Bool) OpenLogicPropNK
olpPropNKCalc = mkTBCalc
    { tbParseForm = purePropFormulaParser thomasBolducZach2019Opts
    , tbParseRule = parseOpenLogicPropNK
    , tbNotation = dropOuterParens
    }

olpPropLKCalc :: TableauCalc PurePropLexicon (Form Bool) OpenLogicPropLK
olpPropLKCalc = gentzenPropLKCalc 
    { tbParseForm = purePropFormulaParser thomasBolducZach2019Opts 
    , tbParseRule = parseOpenLogicPropLK
    , tbNotation = filter (/= '⊤') . dropOuterParens
    }

olpPropLJCalc :: TableauCalc PurePropLexicon (Form Bool) OpenLogicPropLJ
olpPropLJCalc = gentzenPropLJCalc 
    { tbParseForm = purePropFormulaParser thomasBolducZach2019Opts 
    , tbParseRule = parseOpenLogicPropLJ
    , tbNotation = filter (/= '⊤') . dropOuterParens
    }
