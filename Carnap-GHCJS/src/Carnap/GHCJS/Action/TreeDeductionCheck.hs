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
import Carnap.Core.Unification.Unification (MonadVar,FirstOrder)
import Carnap.Core.Unification.ACUI (ACUI)
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Languages.ClassicalSequent.Syntax
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


proofTreeRestriction :: Eq (ClassicalSequentOver lex (Succedent sem)) => ProofTree GentzenPropNJ lex sem -> Restrictor GentzenPropNJ lex
proofTreeRestriction pt _ (As n) = Just noReps
    where noReps _ | allEq . filter (\(Node pl _) -> rule pl == [As n]) $ toListOf leaves pt = 
                        Just "Distinct assumptions are getting the same index"
                   | otherwise = Nothing
          allEq ((Node x _):xs) = all (\(Node pl _) -> content pl == content x) xs
proofTreeRestriction pt _ r = Nothing

checkProofTree :: ( ReLex lex
                  , Sequentable lex
                  , Inference rule lex sem
                  , FirstOrder (ClassicalSequentOver lex)
                  , ACUI (ClassicalSequentOver lex)
                  , MonadVar (ClassicalSequentOver lex) (State Int)
                  , StaticVar (ClassicalSequentOver lex)
                  , Schematizable (lex (ClassicalSequentOver lex))
                  , CopulaSchema (ClassicalSequentOver lex)
                  , Typeable sem
                  ) => TableauCalc lex sem rule -> Value -> IO Value
checkProofTree calc v = case parse parseTreeJSON v of
                           Success t -> case toProofTree calc t of 
                                  Left feedback -> return . toInfo $ feedback
                                  Right tab -> return . toInfo $ validateProofTree $ tab
                           Error s -> do print (show v)
                                         error s

validateProofTree :: ( ReLex lex
                     , Sequentable lex
                     , Inference rule lex sem
                     , FirstOrder (ClassicalSequentOver lex)
                     , ACUI (ClassicalSequentOver lex)
                     , MonadVar (ClassicalSequentOver lex) (State Int)
                     , StaticVar (ClassicalSequentOver lex)
                     , Schematizable (lex (ClassicalSequentOver lex))
                     , CopulaSchema (ClassicalSequentOver lex)
                     , Typeable sem
                     ) => ProofTree rule lex sem -> TreeFeedback lex
validateProofTree t@(Node _ fs) = case hoReduceProofTree (\_ _ -> Nothing) t of
              Left msg -> Node (ProofError msg) (map validateProofTree fs)
              Right seq -> Node (ProofData (show seq)) (map validateProofTree fs)
