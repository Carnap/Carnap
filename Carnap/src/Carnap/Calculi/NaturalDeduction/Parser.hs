{-#LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser where

import Data.Tree
import Data.Either
import Data.List
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Text.Parsec

-----------------------------
--  1. Parsing Deductions  --
-----------------------------

-----------------------------------
--  1.1 Individual Line Parsers  --
-----------------------------------

parseAssertLineFitch :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseAssertLineFitch r f = do dpth  <- indent
                              phi <- f
                              rule <- spaces *> char ':' *> r 
                              intPairs <- many (try parseIntPair <|> parseInt)
                              return $ AssertLine phi rule dpth intPairs
        where parseIntPair = do spaces
                                i1 <- many1 digit
                                char '-'
                                i2 <- many1 digit
                                spaces
                                return ((read i1, read i2) :: (Int,Int))
              parseInt= do spaces
                           i <- many1 digit
                           spaces
                           return ((read i, read i) :: (Int,Int))
                           
parseSeparatorLine :: Parsec String u (DeductionLine r lex a)
parseSeparatorLine = do dpth <- indent
                        char '-'
                        spaces
                        return $ SeparatorLine dpth

parseAssertLine :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseAssertLine r f = do dpth  <- indent
                         phi <- f
                         (rule,deps) <- rline r
                         return $ AssertLine phi rule dpth (map (\x -> (x,x)) deps)

parseShowLine :: Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseShowLine f = do dpth <- indent
                     string "Show" <|> string "show"
                     optional $ char ':'
                     spaces
                     phi <- f <* eof
                     return $ ShowLine phi dpth

parseShowWithLine :: Parsec String u [r] -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseShowWithLine r f = do dpth <- indent
                           string "Show" <|> string "show"
                           optional $ char ':'
                           spaces
                           phi <- f 
                           (rule, deps) <- rline r
                           return $ ShowWithLine phi dpth rule (map (\x->(x,x)) deps)
 
parseQedLine :: Parsec String u [r] -> Parsec String u (DeductionLine r lex a)
parseQedLine r = do dpth <- indent 
                    (rule, deps) <- rline r
                    return $ QedLine rule dpth (map (\x->(x,x)) deps)

-----------------------------------
--  1.2 Deduction style parsers  --
-----------------------------------

toDeduction :: Parsec String () (DeductionLine r lex a) -> String -> [DeductionLine r lex a]
toDeduction parseLine = map handle . lines
        where handle l = 
                case parse parseLine "" l of
                    Right dl -> dl
                    Left e -> PartialLine Nothing e (linedepth l)
              linedepth l = 
                case parse indent "" l of 
                    Right n -> n
                    Left e -> 0

toDeductionMontegue :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> [DeductionLine r lex a]
toDeductionMontegue r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseAssertLine r f) 
                                <|> try (parseShowLine f) 
                                <|> try (parseQedLine r)

toDeductionFitch :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> [DeductionLine r lex a]
toDeductionFitch r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseAssertLineFitch r f) 
                              <|> parseSeparatorLine

toDeductionHardegree :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> [DeductionLine r lex a]
toDeductionHardegree r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseAssertLine r f)
                              <|> parseShowWithLine r f


-----------------------------
--  2. Proof Tree Parsers  --
-----------------------------

-- XXX These are pretty ugly, and should be rewritten. Probably a lot should
-- be folded into methods associated with ND data

{- | 
In a Kalish and Montegue deduction, find the prooftree corresponding to
*line n* in ded, where proof line numbers start at 1
-}
toProofTreeMontegue :: 
    ( Inference r lex
    , Sequentable lex
    ) => Deduction r lex -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex)
toProofTreeMontegue ded n = case ded !! (n - 1)  of
          (AssertLine f r dpth depairs) -> 
                do let deps = map fst depairs
                   mapM_ checkDep deps
                   deps' <- mapM (toProofTreeMontegue ded) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
          (ShowLine f d) -> 
                do m <- matchShow
                   let (QedLine r _ depairs) = ded !! m
                   let deps = map fst depairs
                   mapM_ (checkDep $ m + 1) deps 
                   deps' <- mapM (toProofTreeMontegue ded) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where --for scanning, we ignore the depth of the QED line
                      checkDep m m' = takeRange m' m >>= scan . init
                      matchShow = let ded' = drop n ded in
                          case findIndex (qedAt d) ded' of
                              Nothing -> err "Open subproof (no corresponding QED)"
                              Just m' -> isSubProof n (n + m' - 1)
                      isSubProof n m = case lineRange n m of
                        (h:t) -> if all (\x -> depth x > depth h) t
                                   then Right (m + 1)
                                   else  err $ "Open subproof on lines" ++ show n ++ " to " ++ show m ++ " (no QED in this subproof)"
                        []    -> Right (m+1)
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

{- | 
In a Fitch deduction, find the prooftree corresponding to
*line n* in ded, where proof line numbers start at 1
-}
toProofTreeFitch :: 
    ( Inference r lex
    , Sequentable lex
    ) => Deduction r lex -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex)
toProofTreeFitch ded n = case ded !! (n - 1)  of
          l@(AssertLine f r@(r':_) dpth deps) -> 
                do mapM_ checkDep deps 
                   mapM_ isSP deps
                   if isAssumptionLine l then checkAssumptionLegit else return True
                   dp <- case indirectInference r' of
                        Just (TypedProof prooftype) -> subproofProcess prooftype deps
                        _ -> return . map snd $ deps -- XXX subproofs that don't have an arity just use the last line, e.g. the second of their range.
                                                     -- this is a bit of a hack. All indirect rules should have arities.
                   deps' <- mapM (toProofTreeFitch ded) dp
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep (begin,end) = 
                        case indirectInference r' of 
                            Nothing -> if begin /= end 
                                           then err "you appear to be supplying a line range to a rule of direct proof"
                                           else takeRange end n >>= scan1
                            Just _  -> if begin /= end 
                                                  then do range <- if end + 1 == n 
                                                                      then return [] 
                                                                      else takeRange (end + 1) n
                                                          scan2 range
                                                          checkEnds begin end
                                                  else takeRange end n >>= scan1
                      checkAssumptionLegit 
                        | dpth == 0 = err "you can't make an assumption unless you are beginning a subproof--maybe you forgot to indent?"
                        | n > 1 && dpth <= depth (ded !! (n - 2)) = err "you can't make an assumption unless you are beginning a subproof--maybe you forgot to indent?"
                        | otherwise = return True
                      subproofProcess (ProofType assumptionNumber conclusionNumber) deps = 
                        case filter (\(x,y) -> x /= y) deps of
                            [thesp@(first,last)] | (last - first) < (assumptionNumber + conclusionNumber) -> err "this subproof doesn't have enough lines to apply this rule"
                                                 | let firstlines =  map (\x -> ded !! (x - 1)) (take assumptionNumber [first ..]) in 
                                                     any (not . isAssumptionLine) firstlines  -> 
                                                        err $ "this rule requires the first " ++ show assumptionNumber ++ " lines of the subproof to be assumptions"
                                                 | let lastlines = map (\x -> ded !! (x - 1)) (take conclusionNumber [last, last - 1 ..]) in
                                                     any (\x -> depth x /= depth (ded !! (first - 1))) lastlines -> 
                                                        err $ "the last " ++ show conclusionNumber ++ " lines of the subproof appear not tbe be aligned with the first line"
                                                 | otherwise -> return $  take assumptionNumber [first ..] 
                                                                          ++ take conclusionNumber [last, last - 1 ..] 
                                                                          ++ map fst (delete thesp deps)
                            otherwise -> err "you need to specify exactly one subproof for this rule"
          (PartialLine _ e _) -> Left $ NoParse e n
          (SeparatorLine _) -> Left $ NoResult n
    where err :: String -> Either (ProofErrorMessage lex) a
          err x = Left $ GenericError x n
          ln = length ded
          --line h is accessible by an ordinary inference from the end of
          --the chunk if everything in the chunk has depth greater than or
          --equal to that of line h
          scan1 chunk@(h:_) =
              if all (\x -> depth h <= depth x) chunk
                  then Right True
                  else err "It looks like you're citing a line which is not in your subproof. If that's not what you're doing, you may need to tidy up your proof."
          scan2 [] = Right True
          scan2 chunk@(h:_) = 
              if all (\x -> depth h <= depth x) chunk
                  then Right True
                  else err "it looks like you're citing a subproof that isn't available at this point, since its final line isn't available"
          takeRange m' n' = 
              if n' <= m' 
                      then err "Dependency is later than assertion"
                      else Right $ lineRange m' n'
          --sublist, given by line numbers
          lineRange m n = drop (m - 1) $ take n ded
          checkEnds m n = if m == 1 || depth (ded !! (m - 2)) == depth (ded !! n)
                              then Right True
                              else err "it looks like you're citing a subproof that isn't available at this point, because its first line isn't available."
          isSP (m, n)
            | m == n = Right True
            | depth begin == 0 = err $ "line " ++ show m ++ " must be indented to begin a subproof"
            | m > 1 && depth begin <= depth (ded !! (m - 2)) = err $ "line " ++ show m ++ " must be more indented that the preceding line to begin a subproof"
            | ln > n && depth end <= depth (ded !! n) = err $ "line " ++ show n ++ " must be more indented than the subsequent line to end a subproof"
            | m > n = err "The last line of a subproof cannot come before the first"
            | depth begin /= depth end = err $ "the lines " ++ show m ++ " and " ++ show n ++ " must be vertically aligned to form a subproof"
            | any (\x -> depth x < depth begin) (lineRange m n) = err $ "the lines " ++ show m ++ " and " ++ show n ++ " can't have a less indented line between them, if they are a subproof"
            | not (isAssumptionLine begin) = err $ "the subproof beginning on line " ++ show m ++ " needs to start with an assumption"
            | otherwise = Right True
            -- TODO also impose some "assumption" constraints: subproofs
            -- must begin with assumptions, and this is the only context
            -- where an assumption can occur
            where begin = ded !! (m - 1)
                  end = ded !! (n - 1)


{- | 
In a Hardegree deduction, find the prooftree corresponding to
*line n* in ded, where proof line numbers start at 1
-}
toProofTreeHardegree :: 
    ( Inference r lex
    , Sequentable lex
    ) => Deduction r lex -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex)
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
                            Nothing -> err "This rule is not a rule of indirect proof, and so cannot be used with a show line"
                   deps' <- mapM (toProofTreeHardegree ded) (dp ++ deps)
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
                      matchShow = let ded' = drop n ded in
                          case findIndex (\l -> depth l == d) ded' of
                              Nothing -> isSubProof n (length ded)
                              Just m' -> isSubProof n (n + m')
                      isSubProof n m = case lineRange n m of
                        (h:t) -> if all (\x -> depth x > depth h) t
                                   then Right m
                                   else  err $ "Open subproof on lines" ++ show n ++ " to " ++ show m
                        []    -> Right (m+1)
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

{-|
In an appropriately structured Fitch deduction, find the proof tree
corresponding to *line n*, where proof numbers start at 1
-}
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
                where checkDep (begin,end) = 
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
                                                     | let firstlines =  map (\x -> t .! x) (take assumptionNumber [first ..]) 
                                                           badLine (Just l) = not $ isAssumptionLine l
                                                           badLine Nothing  = True
                                                           in any badLine firstlines  ->
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

--------------------------------------------------------
--Utility functions
--------------------------------------------------------

parseInts :: Parsec String u [Int]
parseInts = do ints <- many1 digit `sepEndBy` separator
               return $ map read ints
    where separator = spaces *> optional (string ",") *> spaces 

rline r = do rule <- spaces *> char ':' *> r 
             deps <- spaces *> parseInts
             return (rule, deps)

--need to handle tabs
indent = do ws <- many $ char ' '
            return $ length ws
