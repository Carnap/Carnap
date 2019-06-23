{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.StructuredFitch (toProofTreeStructuredFitch)
where

import Data.Tree (Tree(Node))
import Data.List (delete)
import Data.Typeable
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ClassicalSequent.Syntax

{-|
In an appropriately structured Fitch deduction, find the proof tree
corresponding to *line n*, where proof numbers start at 1
-}
toProofTreeStructuredFitch :: 
    ( Inference r lex sem
    , Typeable sem
    , Sequentable lex
    ) => DeductionTree r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeStructuredFitch t n = case t .! n of
          Just (l@(AssertLine f r@(r':_) dpth deps)) -> 
                do mapM_ checkDep deps 
                   if isAssumptionLine l then checkAssumptionLegit else return True
                   case indirectInference r' of
                        Just (TypedProof prooftype) -> do dp <- subproofProcess prooftype deps
                                                          deps' <- mapM (toProofTreeStructuredFitch t) dp
                                                          return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                        _ -> do deps' <- mapM (toProofTreeStructuredFitch t . snd) deps
                                return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep :: (Int,Int) -> Either (ProofErrorMessage lex) Bool
                      checkDep (begin,end) = 
                        case indirectInference r' of 
                            Nothing | begin /= end -> err "you appear to be supplying a line range to a rule of direct proof"
                                    | begin `elem` linesFromHere -> Right True
                                    | otherwise ->  err "you appear to be citing a line that is not available"
                            Just _  | begin == end && begin `elem` linesFromHere -> Right True
                                    | (begin,end) `elem` rangesFromHere -> Right True
                                    | otherwise ->  err "you appear to be citing a subproof that is not available or does not exist"
                      checkAssumptionLegit = case subProofOf n t of
                                                 Just (SubProof _ (Leaf k _:_)) | k == n -> return True 
                                                                                | otherwise -> err "Assumptions need to come at the beginning of subproofs"
                                                 _ -> err "Assuptions must occur within subproofs"
                      subproofProcess (ProofType assumptionNumber conclusionNumber) deps = 
                        case filter (\(x,y) -> x /= y) deps of
                            [thesp@(first,last)] -> case range first last t of
                                Just (SubProof _ ls) | (last - first) < (assumptionNumber + conclusionNumber) -> err "this subproof doesn't have enough lines to apply this rule"
                                                     | let firstlines :: Inference r lex sem => DeductionTree r lex sem -> [Maybe (DeductionLine r lex sem)]
                                                           firstlines z =  map (\x -> z .! x) (take assumptionNumber [first ..]) 
                                                           badLine (Just l) = not $ isAssumptionLine l
                                                           badLine Nothing  = True
                                                           checkLines = any badLine
                                                           in checkLines (firstlines t) ->
                                                             err $ "this rule requires the first " ++ show assumptionNumber ++ " lines of the subproof to be assumptions"
                                                     | otherwise -> return $  take assumptionNumber [first ..] 
                                                                              ++ take conclusionNumber [last, last - 1 ..] 
                                                                              ++ map fst (delete thesp deps)
                            otherwise -> err "you need to specify exactly one subproof for this rule"
                                                      
          Just (PartialLine _ e _) -> Left $ NoParse e n
          Just (SeparatorLine _) -> Left $ NoResult n
          Nothing -> err $ "Line " ++ show n ++ " is not a part of this proof"
    where err :: String -> Either (ProofErrorMessage lex) a
          err x = Left $ GenericError x n

          linesOf (Leaf n _) = [n]
          linesOf (SubProof _ ls) = concatMap linesOf ls

          rangesOf (Leaf _ _)  = []
          rangesOf (SubProof r ls) = r : concatMap rangesOf ls

          linesFromHere = case availableLine n t of
                              Nothing -> []
                              Just sp -> linesOf sp

          rangesFromHere = case availableSubproof n t of
                               Nothing -> []
                               Just sp -> rangesOf sp
