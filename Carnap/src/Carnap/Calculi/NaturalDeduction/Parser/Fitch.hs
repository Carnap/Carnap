{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.Fitch (toProofTreeFitch, toDeductionFitch, toDeductionFitchAlt, toCommentedDeductionFitch)
where

import Data.Tree
import Data.Typeable
import Data.List (delete, (\\))
import Text.Parsec
import Carnap.Core.Data.Types
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser

parseAssertLineFitch :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseAssertLineFitch r f = do dpth  <- indent
                              phi <- f
                              rule <- spaces *> char ':' *> r 
                              intPairs <- spaces *> parseIntsAndSpans
                              return $ AssertLine phi rule dpth intPairs
                              
parseAssertLineFitchAlt :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseAssertLineFitchAlt r f = do dpth  <- indent
                                 phi <- f
                                 intPairs <- spaces *> char ':' *> spaces *> parseIntsAndSpans
                                 rule <- r 
                                 return $ AssertLine phi rule dpth intPairs

parseCommentedAssertLineFitch :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseCommentedAssertLineFitch r f = parseAssertLineFitch r f <* optional (char '/' >> many anyChar) <* eof
                           
parseSeparatorLine :: Parsec String u (DeductionLine r lex a)
parseSeparatorLine = SeparatorLine <$> indent <* string "--" <* spaces <* eof
                        
toDeductionFitch :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionFitch r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseAssertLineFitch r f) 
                              <|> try parseSeparatorLine
                              <|> try (parsePartialLine f)
                              --XXX: need triple "try" here to avoid
                              --throwing away errors if first parser fails
                               
toDeductionFitchAlt :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionFitchAlt r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseAssertLineFitchAlt r f) 
                              <|> try parseSeparatorLine
                              <|> try (parsePartialLine f)
                              --XXX: need triple "try" here to avoid
                              --throwing away errors if first parser fails

toCommentedDeductionFitch :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toCommentedDeductionFitch r f = toDeduction (parseLine r f)
        where parseLine r f = try (parseCommentedAssertLineFitch r f) 
                              <|> try parseSeparatorLine
                              <|> try (parsePartialLine f)

{- | 
In a Fitch deduction, find the prooftree corresponding to
*line n* in ded, where proof line numbers start at 1
-}
toProofTreeFitch :: 
    ( Inference r lex sem
    , Sequentable lex
    , Typeable sem
    ) => Deduction r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeFitch ded n = case ded !! (n - 1)  of
          l@(AssertLine f r@(r':_) dpth deps) -> 
                do mapM_ checkDep deps 
                   mapM_ isSP deps
                   mapM_ notBlank deps
                   if isOnlyAssumptionLine l then checkAssumptionLegit else return True
                   dp <- handleArity (indirectInference r')
                   deps' <- mapM (toProofTreeFitch ded) dp
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where handleArity (Just (TypedProof prooftype)) =
                            case filter (\(x,y) -> x /= y) deps of 
                                 [thesp] -> do thesubprems <- subproofProcess prooftype thesp 
                                               return $ thesubprems ++ map fst (delete thesp deps)
                                 _ -> err "you need to specify exactly one subproof for this rule"
                      handleArity (Just (ImplicitProof prooftype))
                            | not (null (filter (\(x,y) -> x /= y) deps)) = err "this rule cannot be used with a line range citation"
                            | otherwise = do let thesp = takePrecedingProof
                                             if null thesp then err "this rule must follow a subproof"
                                                else do let spRange = (n - (length thesp),n - 1)
                                                        checkDep spRange
                                                        isSP spRange
                                                        notBlank spRange
                                                        thesubprems <- subproofProcess prooftype spRange
                                                        return $ thesubprems ++ map fst deps
                      handleArity (Just (PolyTypedProof n prooftype)) =
                            let l = filter (\(x,y) -> x /= y) deps in
                            if length l /= n then err $ "you need to specify exactly " ++ show n ++ " subproofs for this rule"
                                             else do thesubprems <- mapM (subproofProcess prooftype) l
                                                     return $ concat thesubprems ++ map fst (deps \\ l)
                      handleArity (Just (WithAlternate a1 a2)) = either (const $ handleArity $ Just a2) Right (handleArity $ Just a1)
                                                              -- XXX the above is not ideal for producing error messages
                      handleArity _ = return . map snd $ deps -- XXX subproofs that don't have an arity just use the last line, e.g. the second of their range.
                                                              -- this is a bit of a hack. All indirect rules should have arities.

                      notBlank (begin,end) = 
                        case (ded !! (begin - 1), ded !! (end - 1)) of
                            (SeparatorLine _,_) -> err "You appear to be citing a separator line here. This isn't allowed."
                            (_,SeparatorLine _) -> err "You appear to be citing a separator line here. This isn't allowed."
                            _ -> return ()
                      checkDep (begin,end) = 
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
                      subproofProcess (ProofType assumptionNumber conclusionNumber) thesp@(first,last)
                        | (last - first) + 1 < assumptionNumber + conclusionNumber =
                               err $ "the subproof on lines " ++ show first ++ " through " ++ show last ++ " doesn't have enough lines to apply this rule"
                        | let firstlines =  map (\x -> ded !! (x - 1)) (take assumptionNumber [first ..]) in 
                            any (not . isAssumptionLine) firstlines  =
                               err $ "this rule requires the first " ++ show assumptionNumber ++ " lines of a subproof to be assumptions"
                        | let lastlines = map (\x -> ded !! (x - 1)) (take conclusionNumber [last, last - 1 ..]) in
                            any (\x -> depth x /= depth (ded !! (first - 1))) lastlines =
                               err $ "the last " ++ show conclusionNumber 
                                                 ++ " lines of the subproof on lines " 
                                                 ++ show first ++ " through " ++ show last
                                                 ++ " appear not to be be aligned with the first line"
                        | otherwise = return $ take assumptionNumber [first ..] ++ take conclusionNumber [last, last - 1 ..] 
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
          takePrecedingProof = reverse . takeWhile (\x -> depth x > depth (ded !! (n - 1))) . reverse . take (n - 1) $ ded

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
            where begin = ded !! (m - 1)
                  end = ded !! (n - 1)
