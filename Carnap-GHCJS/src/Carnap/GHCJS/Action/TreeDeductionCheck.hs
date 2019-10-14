{-# LANGUAGE FlexibleContexts, OverloadedStrings, CPP, JavaScriptFFI #-}
module Carnap.GHCJS.Action.TreeDeductionCheck (treeDeductionCheckAction) where

import Lib hiding (content)
import Data.Tree
import Data.Either
import Data.Typeable (Typeable)
import Data.Aeson.Types
import qualified Text.Parsec as P (parse) 
import Control.Monad.State (modify,get,execState,State)
import Control.Lens
import Carnap.Core.Unification.Unification (MonadVar,FirstOrder, applySub)
import Carnap.Core.Unification.ACUI (ACUI)
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Calculi.Tableau.Data
import Carnap.Languages.PurePropositional.Logic.Gentzen
import Carnap.GHCJS.Util.ProofJS
import GHCJS.DOM

treeDeductionCheckAction ::  IO ()
treeDeductionCheckAction = runWebGUI $ \w -> 
            do (Just dom) <- webViewGetDomDocument w
               initializeCallback "checkProofTreeInfo" (checkProofTree gentzenPropNJCalc)
               return ()

toProofTree :: ( Typeable sem
               , ReLex lex
               , Sequentable lex
               , Inference rule lex sem
               ) => TableauCalc lex sem rule -> Tree (String,String) -> Either (TreeFeedback lex) (ProofTree rule lex sem)
toProofTree calc (Node (l,r) f) 
    | all isRight parsedForest && isRight newNode = Node <$> newNode <*> sequence parsedForest
    | isRight newNode = Left $ Node Waiting (map cleanTree parsedForest)
    | Left n <- newNode = Left n
    where parsedLabel = (SS . liftToSequent) <$> P.parse (tbParseForm calc) "" l
          parsedRules = P.parse (tbParseRule calc) "" r
          parsedForest = map (toProofTree calc) f
          cleanTree (Left fs) = fs
          cleanTree (Right fs) = fmap (const Waiting) fs
          newNode = case ProofLine 0 <$> parsedLabel <*> parsedRules of
                        Right l -> Right l
                        Left e -> Left (Node (ProofError $ NoParse e 0) (map cleanTree parsedForest))


proofTreeRestriction :: ProofTree GentzenPropNJ PurePropLexicon (Form Bool) -> Restrictor GentzenPropNJ PurePropLexicon
proofTreeRestriction pt _ (As n) = Just noReps
    where noReps _ | allEq (leavesLabeled n pt) = Nothing
                   | otherwise = Just "Distinct assumptions are getting the same index"
          allEq ((Node x _):xs) = all (\(Node pl _) -> content pl == content x) xs
proofTreeRestriction pt _ (IfI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump)
    where assump = SS . liftToSequent $ phin 1
proofTreeRestriction pt _ (IfIVac n) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
proofTreeRestriction pt _ (NegI n) = Just (usesAssumption n pt assump `andFurtherRestriction` exhaustsAssumptions n pt assump )
    where assump = SS . liftToSequent $ phin 1
proofTreeRestriction pt _ (NegIVac n) = Just (usesAssumption n pt (SS . liftToSequent $ phin 1))
proofTreeRestriction pt _ (OrE n m) = Just (usesAssumption n pt (assump 1) 
                                            `andFurtherRestriction` usesAssumption m pt (assump 2)
                                            `andFurtherRestriction` exhaustsAssumptions n pt (assump 1)
                                            `andFurtherRestriction` exhaustsAssumptions m pt (assump 2))
    where assump n = SS . liftToSequent $ phin n
proofTreeRestriction pt _ (OrERVac n m) = Just (usesAssumption n pt (assump 1) 
                                            `andFurtherRestriction` usesAssumption m pt (assump 2)
                                            `andFurtherRestriction` exhaustsAssumptions n pt (assump 1))
    where assump n = SS . liftToSequent $ phin n
proofTreeRestriction pt _ (OrELVac n m) = Just (usesAssumption n pt (assump 1) 
                                            `andFurtherRestriction` usesAssumption m pt (assump 2)
                                            `andFurtherRestriction` exhaustsAssumptions m pt (assump 2))
    where assump n = SS . liftToSequent $ phin n
proofTreeRestriction pt _ (OrEVac n m) = Just (usesAssumption n pt (assump 1) 
                                              `andFurtherRestriction` usesAssumption m pt (assump 2))
    where assump n = SS . liftToSequent $ phin n
proofTreeRestriction pt _ r = Nothing

leavesLabeled :: Int -> ProofTree GentzenPropNJ lex sem -> [ProofTree GentzenPropNJ lex sem]
leavesLabeled n pt = filter (\(Node pl _) -> rule pl == [As n]) $ toListOf leaves pt

usesAssumption n pt assump sub = case leavesLabeled n pt of
              [] -> Nothing
              (Node x _ : _) | content x /= applySub sub assump -> Just "assumption mismatch"
                             | otherwise -> Nothing

exhaustsAssumptions n pt assump sub = if all (`elem` (dischargedList pt)) assumpInstances then Nothing
                                                                                          else Just "This rule will consume an undischarged assumption"
        where dischargedList (Node r f) = dischargedBy (head (rule r)) ++ concatMap dischargedList f

              dischargedBy (IfI n) = [n]
              dischargedBy (IfIVac n) = [n]
              dischargedBy (NegI n) = [n]
              dischargedBy (NegIVac n) = [n]
              dischargedBy (OrE n m) = [n,m]
              dischargedBy (OrELVac n m) = [n,m]
              dischargedBy (OrERVac n m) = [n,m]
              dischargedBy (OrEVac n m) = [n,m]
              dischargedBy _ = []

              theAssump = applySub sub assump

              assumpInstances = concatMap (\(Node pl _) -> case rule pl of [As n] -> [n]; _ -> [])
                              . filter (\(Node pl _) -> content pl == theAssump) 
                              $ toListOf leaves pt

checkProofTree :: ( --ReLex lex
                  -- , Sequentable lex
                  --, Inference rule lex sem
                  -- , FirstOrder (ClassicalSequentOver lex)
                  -- , ACUI (ClassicalSequentOver lex)
                  -- , MonadVar (ClassicalSequentOver lex) (State Int)
                  -- , StaticVar (ClassicalSequentOver lex)
                  -- , Schematizable (lex (ClassicalSequentOver lex))
                  -- , CopulaSchema (ClassicalSequentOver lex)
                  --, Typeable sem
                  ) => TableauCalc PurePropLexicon (Form Bool) GentzenPropNJ -> Value -> IO Value
checkProofTree calc v = case parse parseTreeJSON v of
                           Success t -> case toProofTree calc t of 
                                  Left feedback -> return . toInfo $ feedback
                                  Right tab -> return . toInfo $ validateProofTree $ tab
                           Error s -> do print (show v)
                                         error s

validateProofTree :: ( --ReLex lex
                     --, Sequentable lex
                     ----, Inference rule lex sem
                     --, FirstOrder (ClassicalSequentOver lex)
                     --, ACUI (ClassicalSequentOver lex)
                     --, MonadVar (ClassicalSequentOver lex) (State Int)
                     --, StaticVar (ClassicalSequentOver lex)
                     --, Schematizable (lex (ClassicalSequentOver lex))
                     --, CopulaSchema (ClassicalSequentOver lex)
                     -- , Typeable sem
                     ) => ProofTree GentzenPropNJ PurePropLexicon (Form Bool) -> TreeFeedback PurePropLexicon
validateProofTree t@(Node _ fs) = case hoReduceProofTree (proofTreeRestriction t) t of
              Left msg -> Node (ProofError msg) (map validateProofTree fs)
              Right seq -> Node (ProofData (show seq)) (map validateProofTree fs)
