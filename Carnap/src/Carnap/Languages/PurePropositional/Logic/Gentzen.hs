{-#LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Gentzen
    ( parseGentzenPropLK, gentzenPropLKCalc, GentzenPropLK()
    , parseGentzenPropLJ, gentzenPropLJCalc, GentzenPropLJ()
    , parseGentzenPropNJ, gentzenPropNJCalc, GentzenPropNJ(..)
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
                   | OrIL     | OrIR        | OrE Int Int | OrELVac Int Int | OrERVac Int Int | OrEVac Int Int
                   | IfI Int  | IfIVac Int  | IfE
                   | NegI Int | NegIVac Int | NegE  | FalsumE
                   | As Int
    deriving Eq

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
    show (OrELVac n m) = "∨E (" ++ show n ++ ") (" ++ show m ++ ")"
    show (OrERVac n m) = "∨E (" ++ show n ++ ") (" ++ show m ++ ")"
    show (OrEVac n m) = "∨E (" ++ show n ++ ") (" ++ show m ++ ")"
    show (IfI n) = "⊃I (" ++ show n ++ ")"
    show (IfIVac n) = "⊃I (" ++ show n ++ ")"
    show IfE = "⊃E"
    show (NegI n) = "¬I (" ++ show n ++ ")" 
    show (NegIVac n) = "¬I (" ++ show n ++ ")" 
    show NegE = "¬E"
    show FalsumE = "¬E"
    show (As n) = "(" ++ show n ++ ")"

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
parseGentzenPropNJ = do r <- choice . map try $ (map string [ "&I","&E","/\\I", "/\\E", "∨I", "\\/I" , "⊃E", "->E", ">E",  "¬E", "-E"]
                                    ++ [(\n -> "A" ++ n ) <$> (char '(' *> many1 digit <* char ')')]
                                    ++ [(\n -> "⊃" ++ n ) <$> ((string "->I" <|> string ">I" <|> string "⊃I") *> spaces *> char '(' *> many1 digit <* char ')')]
                                    ++ [(\n -> "¬" ++ n ) <$> ((string "¬I" <|> string "-I") *> spaces *> char '(' *> many1 digit <* char ')')]
                                    ++ [(\n m -> "∨" ++ n ++ "," ++ m) 
                                            <$> ((string "∨E" <|> string "\\/E") *> spaces *> char '(' *> many1 digit <* char ')')
                                            <*> (spaces *> char '(' *> many1 digit <* char ')')])
                                                                                        
                        return $ case r of
                          r | r `elem` ["&I","/\\I"] -> [AndI]
                            | r `elem` ["&E","/\\E"] -> [AndER, AndEL]
                            | r `elem` ["∨I","\\/I"] -> [OrIL, OrIR]
                            | r `elem` ["⊃E",">E", "->E"] -> [IfE]
                            | r `elem` ["¬E","-E"] -> [NegE, FalsumE]
                            | head r == 'A' -> [As (read (tail r) :: Int)]
                            | head r == '⊃' -> let val = read (tail r) :: Int in [IfI val, IfIVac val]
                            | head r == '¬' -> let val = read (tail r) :: Int in [NegI val, NegIVac val]
                            | head r == '∨' -> let val1 = read (takeWhile (/= ',') $ tail r) :: Int
                                                   val2 = read (tail . dropWhile (/= ',') . tail $ r ) :: Int
                                                   in [OrE val1 val2, OrELVac val1 val2, OrERVac val1 val2, OrEVac val1 val2]
                            | otherwise -> error $ "unrecognized:" ++ r

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
         coreRuleOf (OrELVac n m) = proofByCasesVariations !! 1
         coreRuleOf (OrERVac n m) = proofByCasesVariations !! 2
         coreRuleOf (OrEVac n m) = proofByCasesVariations !! 3
         coreRuleOf (IfI n) = conditionalProofVariations !! 0
         coreRuleOf (IfIVac n) = conditionalProofVariations !! 1
         coreRuleOf IfE = modusPonens
         coreRuleOf (NegI n) = constructiveFalsumReductioVariations !! 0
         coreRuleOf (NegIVac n) = constructiveFalsumReductioVariations !! 1
         coreRuleOf NegE = falsumIntroduction
         coreRuleOf FalsumE = falsumElimination
         coreRuleOf (As n) = axiom

instance Inference GentzenPropNJ PurePropLexicon (Form Bool) where
        ruleOf x = coreRuleOf x

instance StructuralInference GentzenPropNJ PurePropLexicon (ProofTree GentzenPropNJ PurePropLexicon (Form Bool)) where
    structuralRestriction pt _ (As n) = Just noReps
        where noReps _ | allEq (leavesLabeled n pt) = Nothing
                       | otherwise = Just "Distinct assumptions are getting the same index"
              allEq ((Node x _):xs) = all (\(Node pl _) -> content pl == content x) xs
    structuralRestriction pt _ (IfI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump)
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (IfIVac n) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (NegI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump )
        where assump = SS . liftToSequent $ phin 1
    structuralRestriction pt _ (NegIVac n) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
    structuralRestriction pt _ (OrE n m) = Just (usesAssumption n pt (assump 1) 
                                                `andFurtherRestriction` usesAssumption m pt (assump 2)
                                                `andFurtherRestriction` exhaustsAssumptions n pt (assump 1)
                                                `andFurtherRestriction` exhaustsAssumptions m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrERVac n m) = Just (usesAssumption n pt (assump 1) 
                                                `andFurtherRestriction` usesAssumption m pt (assump 2)
                                                `andFurtherRestriction` exhaustsAssumptions n pt (assump 1))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrELVac n m) = Just (usesAssumption n pt (assump 1) 
                                                `andFurtherRestriction` usesAssumption m pt (assump 2)
                                                `andFurtherRestriction` exhaustsAssumptions m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ (OrEVac n m) = Just (usesAssumption n pt (assump 1) 
                                                  `andFurtherRestriction` usesAssumption m pt (assump 2))
        where assump n = SS . liftToSequent $ phin n
    structuralRestriction pt _ r = Nothing

instance AssumptionNumbers GentzenPropNJ where
        introducesAssumptions (As n) = [n]
        introducesAssumptions _ = []

        dischargesAssumptions (IfI n) = [n]
        dischargesAssumptions (IfIVac n) = [n]
        dischargesAssumptions (NegI n) = [n]
        dischargesAssumptions (NegIVac n) = [n]
        dischargesAssumptions (OrE n m) = [n,m]
        dischargesAssumptions (OrELVac n m) = [n,m]
        dischargesAssumptions (OrERVac n m) = [n,m]
        dischargesAssumptions (OrEVac n m) = [n,m]
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
