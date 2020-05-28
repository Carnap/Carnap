{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.Hardegree (toProofTreeHardegree, toDeductionHardegree)
where

import Data.Tree
import Data.Typeable
import Data.List (findIndex)
import Text.Parsec
import Carnap.Core.Data.Types
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser

parseShowWithLine :: Parsec String u [r] -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseShowWithLine r f = do dpth <- indent
                           string "Show" <|> string "show"
                           optional $ char ':'
                           spaces
                           phi <- f 
                           (rule, deps) <- rline r
                           return $ ShowWithLine phi dpth rule (map (\x->(x,x)) deps)

toDeductionHardegree :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionHardegree r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseAssertLine r f)
                              <|> try (parseShowWithLine r f)
                              <|> try (parsePartialLine f)
                              --XXX: need double "try" here to avoid
                              --throwing away errors if first parser fails

{- | 
In a Hardegree deduction, find the prooftree corresponding to
*line n* in ded, where proof line numbers start at 1
-}
toProofTreeHardegree :: 
    ( Inference r lex sem
    , Sequentable lex
    , Typeable sem
    ) => Deduction r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeHardegree ded n = case ded !! (n - 1)  of
          (AssertLine f r dpth depairs) -> 
                do let deps = map fst depairs
                   mapM_ checkDep deps
                   deps' <- mapM (toProofTreeHardegree ded) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
          (ShowWithLine f d r@(r':_) depairs) -> 
                do m <- matchShow --the last line of the subproof
                   let deps = map fst depairs
                   mapM_ checkDep deps
                   dp <- case indirectInference r' of
                            Just (TypedProof prooftype) -> subproofProcess prooftype (n + 1) m
                            Just (DeferTo k) | length ded < (n + 1) -> err "Waiting on context to determine proof type"
                                             | otherwise -> case ruleOfLine (ded !! ((n - 1) + k)) >>= indirectInference . head of
                                                                (Just (DeferredTo (TypedProof prooftype))) -> subproofProcess prooftype (n + 1) m
                                                                _ -> subproofProcess (ProofType 0 . length $ premisesOf r') (n + 1) m
                            _ -> subproofProcess (ProofType 0 . length $ premisesOf r') (n + 1) m --Hardegree allows this, and it's rather nice in his notation
                   deps' <- mapM (toProofTreeHardegree ded) (dp ++ deps)
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
                      --For this system, extra subproof deps need to occur
                      --outside of the subproof, i.e. be available from the
                      --show line. Arbitrary choice on my part.
                      matchShow = let ded' = drop n ded in
                          case findIndex (\l -> depth l <= d) ded' of
                              Nothing -> Right (length ded)
                              Just m' -> Right (n + m')
                                  -- XXX: since we're looking for the line number, starting at 1,
                                  -- the index (starting at zero) of the next line is actually what we want
          (PartialLine _ e _) -> Left $ NoParse e n

    where err :: String -> Either (ProofErrorMessage lex) a
          err x = Left $ GenericError x n
          ln = length ded
          --line h is accessible from the end of the chunk if everything in
          --the chunk has depth greater than or equal to that of line h,
          --and h is not a show line with no matching QED
          scan chunk@(h:t) =
              if all (\x -> depth h <= depth x) chunk
                  then case h of
                    (ShowWithLine _ _ _ _) -> if any (\x -> depth h == depth x) t
                        then Right True
                        else err "To cite a show line at this point, the line be available---the associated subproof must be closed above this point."
                    _ -> Right True
                  else err "It looks like you're citing a line which is not in your subproof. If you're not, you may need to tidy up your proof."
          takeRange m' n' = 
              if n' <= m' 
                      then err "Dependency is later than assertion"
                      else Right $ lineRange m' n'
          --sublist, given by line numbers
          lineRange m n = drop (m - 1) $ take n ded
          subproofProcess (ProofType assumptionNumber conclusionNumber) first last 
               | length available < (assumptionNumber + conclusionNumber) = err "this subproof doesn't have enough available lines to apply this rule"
               | let firstlines =  map (\x -> ded !! (x - 1)) (take assumptionNumber available) in 
                   any (not . isAssumptionLine) firstlines  =
                      err $ "this rule requires the first " ++ show assumptionNumber ++ " available lines of the subproof to be assumptions"
               | otherwise = return $ take assumptionNumber available ++ drop (length available - conclusionNumber) available
               where available = filter (\x -> depth (ded !! (x - 1)) == depth (ded !! (first - 1))) [first .. last]
