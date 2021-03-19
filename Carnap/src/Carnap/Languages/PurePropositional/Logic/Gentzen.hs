{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gentzen
    ( parseGentzenPropLK, gentzenPropLKCalc, GentzenPropLK()
    , parseGentzenPropLJ, gentzenPropLJCalc, GentzenPropLJ()
    , parseGentzenPropNJ, gentzenPropNJCalc, GentzenPropNJ()
    , parseGentzenPropNK, gentzenPropNKCalc, GentzenPropNK()
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

data GentzenPropLK = Ax    | Cut   | XL | XR | CL | CR | WL | WR
                   | AndL1 | AndL2 | AndR
                   | OrR1  | OrR2  | OrL
                   | CondR | CondL
                   | NegR  | NegL
    deriving Eq

newtype GentzenPropLJ = LJ GentzenPropLK

data GentzenPropNJ = AndI     | AndEL       | AndER
                   | OrIL     | OrIR        | OrE Int Int | OrELVac (Maybe Int) Int 
                   | OrERVac Int (Maybe Int)| OrEVac (Maybe Int) (Maybe Int)
                   | IfI Int  | IfIVac (Maybe Int)  | IfE
                   | NegI Int | NegIVac (Maybe Int) | NegE  | FalsumE
                   | As Int
                   | Pr
    deriving Eq

data GentzenPropNK = NJ GentzenPropNJ 
                   | LEM
    deriving Eq

instance Show GentzenPropLK where
    show Ax     = "Ax"
    show Cut    = "Cut"
    show AndL1  = "&L"
    show AndL2  = "&L"
    show AndR   = "&R"
    show OrR1   = "∨R" 
    show OrR2   = "∨R"
    show OrL    = "∨L"
    show CondR  = "→R"
    show CondL  = "→R"
    show NegR   = "¬R" 
    show NegL   = "¬L"
    show XL     = "XL"
    show XR     = "XR"
    show CL     = "CL"
    show CR     = "CR"
    show WL     = "WL"
    show WR     = "WR"

instance Show GentzenPropLJ where
    show (LJ x) = show x

instance Show GentzenPropNJ where
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
    show NegE = "¬E"
    show FalsumE = "¬E"
    show (As n) = "(" ++ show n ++ ")"
    show Pr = "Pr"

instance Show GentzenPropNK where
    show (NJ x) = show x
    show LEM = "LEM"

parseGentzenPropLK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [GentzenPropLK]
parseGentzenPropLK rtc =  do 
     r <- choice (map (try . string) [ "Ax", "Cut"
                 , "WL","WR","XL","XR","CL","CR"
                 , "&R","∧R","/\\R"
                 , "&L","∧L","/\\L"
                 , "∨L","vL","\\/L"
                 , "∨R","vR","\\/R"
                 , "→L","->L", ">L"
                 , "→R","->R", ">R"
                 , "¬L","~L","-L"
                 , "¬R","~R","-R"
                 ])
     return $ case r of
        r | r == "Ax" -> [Ax]
          | r == "XL" -> [XL]
          | r == "WL" -> [WL]
          | r == "CL" -> [CL]
          | r == "XR" -> [XR]
          | r == "WR" -> [WR]
          | r == "CR" -> [CR]
          | r == "Cut" -> [Cut]
          | r `elem` ["&R","∧R","/\\R"] -> [AndR]
          | r `elem` ["&L","∧L","/\\L"] -> [AndL1, AndL2]
          | r `elem` ["∨L","vL","\\/L"] -> [OrL]
          | r `elem` ["∨R","vR","\\/R"] -> [OrR1, OrR2]
          | r `elem` ["→L","->L", ">L"] -> [CondL]
          | r `elem` ["→R","->R", ">R"] -> [CondR]
          | r `elem` ["¬L","~L","-L"] -> [NegL]
          | r `elem` ["¬R","~R","-R"] -> [NegR]

parseGentzenPropLJ rtc = map LJ <$> parseGentzenPropLK rtc

parseGentzenPropNJ :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [GentzenPropNJ]
parseGentzenPropNJ rtc = choice . map try $
                        [ stringOpts ["&I","/\\I"] >> return [AndI]
                        , stringOpts ["&E","/\\E"] >> return [AndER, AndEL]
                        , stringOpts  ["∨I","\\/I"] >> return [OrIL, OrIR]
                        , stringOpts ["⊃E",">E", "->E"] >> return [IfE]
                        , stringOpts ["¬E","-E"] >> return [NegE, FalsumE]
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
                        , eof >> return [Pr]
                        ]
    where stringOpts = choice . map (try . string)

parseGentzenPropNK :: RuntimeDeductionConfig lex (Form Bool) -> Parsec String u [GentzenPropNK]
parseGentzenPropNK rtc = (map NJ <$> parseGentzenPropNJ rtc) <|> (string "LEM" >> return [LEM])

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         ) => CoreInference GentzenPropLK lex (Form Bool) where
         corePremisesOf AndL1 = [ SA (phin 1) :+: GammaV 1  :|-: DeltaV 1]
         corePremisesOf AndL2 = [ SA (phin 2) :+: GammaV 1  :|-: DeltaV 1]
         corePremisesOf AndR  = [ GammaV 1 :|-: DeltaV 1 :-: SS (phin 1)
                                , GammaV 1 :|-: DeltaV 1 :-: SS (phin 2)
                                ]
         corePremisesOf OrR1  = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 1) ]
         corePremisesOf OrR2  = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 2) ]
         corePremisesOf OrL   = [ SA (phin 1) :+: GammaV 1 :|-: DeltaV 1
                                , SA (phin 2) :+: GammaV 1 :|-: DeltaV 1
                                ] 
         corePremisesOf CondL = [ GammaV 1 :|-: DeltaV 1 :-: SS (phin 1)
                                , SA (phin 2) :+: GammaV 2 :|-: DeltaV 2
                                ]
         corePremisesOf CondR = [ SA (phin 1) :+: GammaV 1 :|-:  DeltaV 1 :-: SS (phin 2)]
         corePremisesOf NegL  = [ GammaV 1 :|-:  DeltaV 1 :-: SS (phin 1)]
         corePremisesOf NegR  = [ SA (phin 1) :+: GammaV 1 :|-:  DeltaV 1 ]
         corePremisesOf CL    = [ GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf CR    = [ GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf XL    = [ GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf XR    = [ GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf WL    = [ GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf WR    = [ GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf Cut   = [ SA (phin 1) :+: GammaV 1 :|-: DeltaV 1
                                , GammaV 2 :|-: DeltaV 2 :-: SS (phin 1)
                                ]
         corePremisesOf Ax    = []

         coreConclusionOf AndL1 = SA (phin 1 ./\. phin 2) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf AndL2 = SA (phin 1 ./\. phin 2) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf AndR  = GammaV 1 :|-: DeltaV 1 :-: SS (phin 1 ./\. phin 2)
         coreConclusionOf OrR1  = GammaV 1 :|-: DeltaV 1 :-: SS (phin 1 .\/. phin 2)
         coreConclusionOf OrR2  = GammaV 1 :|-: DeltaV 1 :-: SS (phin 1 .\/. phin 2)
         coreConclusionOf OrL   = SA (phin 1 .\/. phin 2) :+: GammaV 1 :|-:  DeltaV 1
         coreConclusionOf CondL = SA (phin 1 .=>. phin 2) :+: GammaV 1 :+: GammaV 2 :|-:  DeltaV 1 :-: DeltaV 2
         coreConclusionOf CondR = GammaV 1  :|-: DeltaV 1 :-: SS (phin 1 .=>. phin 2)
         coreConclusionOf NegL  = SA (lneg $ phin 1) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf NegR  = GammaV 1 :|-:   DeltaV 1 :-: SS (lneg $ phin 1)
         coreConclusionOf CL    = GammaV 1 :|-: DeltaV 1
         coreConclusionOf CR    = GammaV 1 :|-: DeltaV 1
         coreConclusionOf XL    = GammaV 1 :|-: DeltaV 1
         coreConclusionOf XR    = GammaV 1 :|-: DeltaV 1
         coreConclusionOf WR    = GammaV 1 :|-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf WL    = GammaV 2 :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf Cut   = GammaV 1 :+: GammaV 2 :|-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf Ax    = SA (phin 1) :|-: SS (phin 1)

instance SpecifiedUnificationType GentzenPropLK

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference GentzenPropLJ lex (Form Bool) where
         corePremisesOf (LJ x) = corePremisesOf x

         coreConclusionOf (LJ x) = coreConclusionOf x

         coreRestriction x = Just $ \sub -> monoConsequent (applySub sub $ coreConclusionOf x)
             where monoConsequent :: forall lex . Eq (ClassicalSequentOver lex (Form Bool)) => ClassicalSequentOver lex (Sequent (Form Bool)) -> Maybe String
                   monoConsequent (_:|-:x)= case nub (toListOf concretes x :: [ClassicalSequentOver lex (Form Bool)]) of
                                              _:_:xs -> Just "LJ requires that the right hand side of each sequent contain at most one formula"
                                              _ -> Nothing

instance SpecifiedUnificationType GentzenPropLJ

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference GentzenPropNJ lex (Form Bool) where
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

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference GentzenPropNK lex (Form Bool) where
         coreRuleOf (NJ x) = coreRuleOf x
         coreRuleOf LEM = [] ∴ Top :|-: SS (phin 1 .\/. (lneg $ phin 1))

instance Inference GentzenPropNJ PurePropLexicon (Form Bool) where
        ruleOf x = coreRuleOf x

instance Inference GentzenPropNK PurePropLexicon (Form Bool) where
        ruleOf x = coreRuleOf x

instance (Eq r, AssumptionNumbers r) => StructuralInference GentzenPropNJ PurePropLexicon (ProofTree r PurePropLexicon (Form Bool)) where
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

instance (Eq r, AssumptionNumbers r) => StructuralInference GentzenPropNK PurePropLexicon (ProofTree r PurePropLexicon (Form Bool)) where
    structuralRestriction pt y (NJ x) = structuralRestriction pt y x
    structuralRestriction pt _ r = Nothing

instance StructuralOverride GentzenPropNJ (ProofTree r PurePropLexicon (Form Bool))

instance StructuralOverride GentzenPropNK (ProofTree r PurePropLexicon (Form Bool))

instance AssumptionNumbers GentzenPropNJ where
        introducesAssumptions (As n) = [n]
        introducesAssumptions Pr = [-1] 
        --XXX: premises introduce assumptions that can't be discharged.
        introducesAssumptions _ = []

        dischargesAssumptions (IfI n) = [n]
        dischargesAssumptions (IfIVac (Just n)) = [n]
        dischargesAssumptions (NegI n) = [n]
        dischargesAssumptions (NegIVac (Just n)) = [n]
        dischargesAssumptions (OrE n m) = [n,m]
        dischargesAssumptions (OrELVac (Just n) m) = [n,m]
        dischargesAssumptions (OrELVac Nothing m) = [m]
        dischargesAssumptions (OrERVac n (Just m)) = [n,m]
        dischargesAssumptions (OrERVac n Nothing) = [n]
        dischargesAssumptions (OrEVac (Just n) (Just m)) = [n,m]
        dischargesAssumptions (OrEVac (Just n) Nothing) = [n]
        dischargesAssumptions (OrEVac Nothing (Just m)) = [m]
        dischargesAssumptions _ = []

instance AssumptionNumbers GentzenPropNK where
        introducesAssumptions (NJ x) = introducesAssumptions x
        introducesAssumptions _ = []

        dischargesAssumptions (NJ x) = dischargesAssumptions x
        dischargesAssumptions _ = []

gentzenPropNJCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropNJ
gentzenPropNJCalc = mkTBCalc
    { tbParseForm = purePropFormulaParser hardegreeOpts
    , tbParseRule = parseGentzenPropNJ
    }

gentzenPropNKCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropNK
gentzenPropNKCalc = mkTBCalc
    { tbParseForm = purePropFormulaParser hardegreeOpts
    , tbParseRule = parseGentzenPropNK
    }

gentzenPropLKCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLK
gentzenPropLKCalc = mkTBCalc
    { tbParseForm = langParser
    , tbParseRule = parseGentzenPropLK
    }

gentzenPropLJCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLJ
gentzenPropLJCalc = mkTBCalc
    { tbParseForm = langParser
    , tbParseRule = parseGentzenPropLJ
    }
