{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.Montague (toProofTreeMontague, toDeductionMontague)
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

parseShowLine :: Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseShowLine f = do dpth <- indent
                     try (string "Show") <|> string "show" <|> string "SHOW"
                     optional $ char ':'
                     spaces
                     phi <- f <* eof
                     return $ ShowLine phi dpth

parseQedLine :: Parsec String u [r] -> Parsec String u (DeductionLine r lex a)
parseQedLine r = do dpth <- indent 
                    (rule, deps) <- rline r
                    return $ QedLine rule dpth (map (\x->(x,x)) deps)

toDeductionMontague :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionMontague r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseAssertLine r f) 
                              <|> try (parseShowLine f) 
                              <|> try (parseQedLine r) 
                              <|> try (parsePartialLine f) 

{- | 
In a Kalish and Montague deduction, find the prooftree corresponding to
*line n* in ded, where proof line numbers start at 1
-}
toProofTreeMontague :: 
    ( Inference r lex sem
    , Sequentable lex
    , Typeable sem
    ) => Deduction r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeMontague ded n = case ded !! (n - 1)  of
          (AssertLine f r@(r':_) dpth depairs) -> 
                do let deps = map fst depairs
                   mapM_ checkDep deps
                   deps' <- mapM (toProofTreeMontague ded) deps
                   case indirectInference r' of 
                        Just _ -> err $ "it appears you're trying to use a rule of indirect inference to make a direct inference, rather than to close a subproof"
                        Nothing -> return ()
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
          (ShowLine f d) -> 
                do m <- matchShow
                   let (QedLine r _ depairs) = ded !! m
                   let deps = map fst depairs
                   mapM_ (checkDep $ m + 1) deps 
                   deps' <- mapM (toProofTreeMontague ded) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where --for scanning, we ignore the depth of the QED line
                      checkDep m m' = takeRange m' m >>= scan . init
                      matchShow = let ded' = drop n ded in
                          case findIndex (qedAt d) ded' of
                              Nothing -> err "Open subproof (no corresponding QED)"
                              Just m' -> isSubProof n (n + m')
                      isSubProof n m = case lineRange n m of
                        (h:t) -> if all (\x -> depth x > depth h) t
                                   then Right m 
                                   else err $ "Open subproof starting on " ++ show n ++ " (indented subproof ends before QED line at " ++ show (m + 1) ++ ")"
                        []    -> Right (m + 1)
                      qedAt d (QedLine _ dpth _) = d == dpth
                      qedAt d _ = False
          (QedLine _ _ _) -> err "A QED line cannot be cited as a justification" 
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
                    (ShowLine _ _) -> if any (\x -> depth h == depth x) t
                        then Right True
                        else err "To cite a show line at this point, the line be available---it must have a matching QED earlier than this line."
                    _ -> Right True
                  else err "It looks like you're citing a line which is not in your subproof. If you're not, you may need to tidy up your proof."
          takeRange m' n' = 
              if n' <= m' 
                      then err "Dependency is later than assertion"
                      else Right $ lineRange m' n'
          --sublist, given by line numbers
          lineRange m n = drop (m - 1) $ take n ded
