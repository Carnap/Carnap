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

data GentzenPropLK = Ax    | Rep   | Cut
                   | AndL1 | AndL2 | AndR
                   | OrR1  | OrR2  | OrL
                   | CondR | CondL
                   | NegR  | NegL

newtype GentzenPropLJ = LJ GentzenPropLK

data GentzenPropNJ = AndI     | AndEL       | AndER
                   | OrIL     | OrIR        | OrE Int Int | OrELVac (Maybe Int) Int 
                   | OrERVac Int (Maybe Int)| OrEVac (Maybe Int) (Maybe Int)
                   | IfI Int  | IfIVac (Maybe Int)  | IfE
                   | NegI Int | NegIVac (Maybe Int) | NegE  | FalsumE
                   | As Int
    deriving Eq

data GentzenPropNK = NJ GentzenPropNJ | LEM

instance Show GentzenPropLK where
    show Ax     = "Ax"
    show Rep    = "Rep"
    show Cut    = "Cut"
    show AndL1  = "L&1"
    show AndL2  = "L&2"
    show AndR   = "R&"
    show OrR1   = "R∨1" 
    show OrR2   = "R∨2"
    show OrL    = "L∨"
    show CondR  = "R→"
    show CondL  = "L→"
    show NegR   = "R¬" 
    show NegL   = "L¬"

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

instance Show GentzenPropNK where
    show (NJ x) = show x
    show LEM = "LEM"

parseGentzenPropLK :: Parsec String u [GentzenPropLK]
parseGentzenPropLK =  do r <- choice (map (try . string) [ "Ax", "Rep", "Cut"
                                                         , "R&","R∧","R/\\"
                                                         ,"L&1","L∧1","L/\\1"
                                                         ,"L&2","L∧2","L/\\2"
                                                         , "L∨","Lv","L\\/"
                                                         ,"R∨1","Rv1","R\\/1"
                                                         ,"R∨2","Rv2","R\\/2"
                                                         , "L→","L->"
                                                         , "R→","R->"
                                                         , "L¬","L~","L-"
                                                         , "R¬","R~","R-"
                                                         ])
                         return $ (\x -> [x]) $ case r of
                            r | r == "Ax" -> Ax
                              | r == "Rep" -> Rep
                              | r == "Cut" -> Cut
                              | r `elem` ["R&","R∧","R/\\"] -> AndR
                              | r `elem` ["L&1","L∧1","L/\\1"] -> AndL1
                              | r `elem` ["L&2","L∧2","L/\\2"] -> AndL2
                              | r `elem` ["L∨","Lv","L\\/"] -> OrL
                              | r `elem` ["R∨1","Rv1","R\\/1"] -> OrR1
                              | r `elem` ["R∨2","Rv2","R\\/2"] -> OrR2
                              | r `elem` ["L→","L->"] -> CondL
                              | r `elem` ["R→","R->"] -> CondR
                              | r `elem` ["L¬","L~","L-"] -> NegL
                              | r `elem` ["R¬","R~","R-"] -> NegR

parseGentzenPropLJ = map LJ <$> parseGentzenPropLK

parseGentzenPropNJ :: Parsec String u [GentzenPropNJ]
parseGentzenPropNJ = choice . map try $
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
                        ]
    where stringOpts = choice . map (try . string)

parseGentzenPropNK :: Parsec String u [GentzenPropNK]
parseGentzenPropNK = (map NJ <$> parseGentzenPropNJ) <|> (string "LEM" >> return [LEM])

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         ) => CoreInference GentzenPropLK lex (Form Bool) where
         corePremisesOf AndL1 = [SA (phin 1) :+: GammaV 1 :|-: DeltaV 1]
         corePremisesOf AndL2 = [SA (phin 2) :+: GammaV 1 :|-: DeltaV 1]
         corePremisesOf AndR = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1
                               , GammaV 2 :|-: SS (phin 2) :-: DeltaV 2
                               ]
         corePremisesOf OrR1 = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 1)]
         corePremisesOf OrR2 = [ GammaV 1 :|-: DeltaV 1 :-: SS(phin 2)]
         corePremisesOf OrL  = [ GammaV 1 :+: SA (phin 1) :|-: DeltaV 1
                               , GammaV 2 :+: SA (phin 1) :|-: DeltaV 2
                               ] 
         corePremisesOf CondL = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1
                                , GammaV 2 :+: SA (phin 2) :|-: DeltaV 2
                                ]
         corePremisesOf CondR = [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) :-: DeltaV 2 ]
         corePremisesOf NegL = [ GammaV 1 :|-: SS (phin 1) :-: DeltaV 1 ]
         corePremisesOf NegR = [ SA (phin 1) :+: GammaV 1 :|-:  DeltaV 1 ]
         corePremisesOf Rep =  [GammaV 1 :|-: DeltaV 1 ]
         corePremisesOf Cut =  [ SA (phin 1) :+: GammaV 1 :|-: DeltaV 1 
                               , GammaV 2 :|-: DeltaV 2 :-: SS (phin 1)
                               ]
         corePremisesOf Ax = [] 

         coreConclusionOf AndL1 = SA (phin 1 ./\. phin 2) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf AndL2 = SA (phin 1 ./\. phin 2) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf AndR = GammaV 1 :+: GammaV 2 :|-: SS (phin 1 ./\. phin 2) :-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf OrR1 =  GammaV 1 :|-: SS (phin 1 .\/. phin 2) :-: DeltaV 1
         coreConclusionOf OrR2 = GammaV 1 :|-: SS (phin 1 .\/. phin 2) :-: DeltaV 1
         coreConclusionOf OrL = SA (phin 1 .\/. phin 2) :+: GammaV 1 :+: GammaV 2 :|-:  DeltaV 1 :-: DeltaV 2
         coreConclusionOf CondL = SA (phin 1 .=>. phin 2) :+: GammaV 1 :+: GammaV 2 :|-:  DeltaV 1 :-: DeltaV 2
         coreConclusionOf CondR =  GammaV 1 :+: GammaV 2 :|-:  SS (phin 1 .=>. phin 2) :-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf NegL = SA (lneg $ phin 1) :+: GammaV 1 :|-: DeltaV 1
         coreConclusionOf NegR =  GammaV 1 :|-: SS (lneg $ phin 1) :-: DeltaV 1
         coreConclusionOf Rep =  GammaV 1 :|-: DeltaV 1 
         coreConclusionOf Cut =  GammaV 1 :+: GammaV 2 :|-: DeltaV 1 :-: DeltaV 2
         coreConclusionOf Ax =  GammaV 1 :+: SA (phin 1) :|-: SS (phin 1) :-: DeltaV 1 

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

instance ( BooleanLanguage (ClassicalSequentOver lex (Form Bool))
         , BooleanConstLanguage (ClassicalSequentOver lex (Form Bool))
         , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form Bool))
         , PrismSubstitutionalVariable lex
         , FirstOrderLex (lex (ClassicalSequentOver lex))
         , Eq (ClassicalSequentOver lex (Form Bool))
         , ReLex lex
         ) => CoreInference GentzenPropNK lex (Form Bool) where
         coreRuleOf (NJ x) = coreRuleOf x
         coreRuleOf LEM = [] ∴ Top :|-: SS (phin 1 .\/. phin 2)

instance Inference GentzenPropNJ PurePropLexicon (Form Bool) where
        ruleOf x = coreRuleOf x

instance Inference GentzenPropNK PurePropLexicon (Form Bool) where
        ruleOf x = coreRuleOf x

instance AssumptionNumbers r => StructuralInference GentzenPropNJ PurePropLexicon (ProofTree r PurePropLexicon (Form Bool)) where
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
    structuralRestriction pt _ (OrE n m) = Just (usesAssumption n pt (assump 1) 
                                                `andFurtherRestriction` usesAssumption m pt (assump 2)
                                                `andFurtherRestriction` exhaustsAssumptions n pt (assump 1)
                                                `andFurtherRestriction` exhaustsAssumptions m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
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

instance AssumptionNumbers r => StructuralInference GentzenPropNK PurePropLexicon (ProofTree r PurePropLexicon (Form Bool)) where
    structuralRestriction pt y (NJ x) = structuralRestriction pt y x
    structuralRestriction pt _ r = Nothing

instance AssumptionNumbers GentzenPropNJ where
        introducesAssumptions (As n) = [n]
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

leavesLabeled :: AssumptionNumbers rule => Int -> ProofTree rule lex sem -> [ProofTree rule lex sem]
leavesLabeled n pt = filter (\(Node pl _) -> introducesAssumptions (head (rule pl)) == [n]) $ toListOf leaves pt

usesAssumption n pt assump sub = case leavesLabeled n pt of
              [] -> Nothing
              (Node x _ : _) | content x /= applySub sub assump -> Just "assumption mismatch"
                             | otherwise -> Nothing

exhaustsAssumptions n pt assump sub = if all (`elem` (dischargedList pt)) assumpInstances then Nothing
                                                                                          else Just "This rule will consume an undischarged assumption"
        where dischargedList (Node r f) = dischargesAssumptions (head (rule r)) ++ concatMap dischargedList f
              theAssump = applySub sub assump
              assumpInstances = concatMap (\(Node pl _) -> case rule pl of [r] -> introducesAssumptions r; _ -> [])
                              . filter (\(Node pl _) -> content pl == theAssump) 
                              $ toListOf leaves pt

gentzenPropNJCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropNJ
gentzenPropNJCalc = TableauCalc 
    { tbParseForm = purePropFormulaParser hardegreeOpts
    , tbParseRule = parseGentzenPropNJ
    }

gentzenPropNKCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropNK
gentzenPropNKCalc = TableauCalc 
    { tbParseForm = purePropFormulaParser hardegreeOpts
    , tbParseRule = parseGentzenPropNK
    }

gentzenPropLKCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLK
gentzenPropLKCalc = TableauCalc 
    { tbParseForm = langParser
    , tbParseRule = parseGentzenPropLK
    }

gentzenPropLJCalc :: TableauCalc PurePropLexicon (Form Bool) GentzenPropLJ
gentzenPropLJCalc = TableauCalc 
    { tbParseForm = langParser
    , tbParseRule = parseGentzenPropLJ
    }
