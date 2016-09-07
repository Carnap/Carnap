{-#LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser 

where

import Data.Tree
import Data.Either
import Data.List
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Parser
import Carnap.Calculi.NaturalDeduction.Syntax
import Text.Parsec

toDeduction :: Parsec String () [r] -> Parsec String () (FixLang lex a) -> String 
    -> [Either ParseError (DeductionLine r lex a)]
toDeduction r f = map (parse (parseLine r f) "") . lines

type MultiRule r = [r]

data DeductionLine r lex a where
        AssertLine :: 
            { asserted :: FixLang lex a
            , assertRule :: [r]
            , assertDepth :: Int
            , assertDependencies :: [Int]
            } -> DeductionLine r lex a
        ShowLine :: 
            { toShow :: FixLang lex a
            , showDepth :: Int
            } -> DeductionLine r lex a
        QedLine :: 
            { closureRule :: [r]
            , closureDepth :: Int
            , closureDependencies :: [Int]
            } -> DeductionLine r lex a

depth (AssertLine _ _ dpth _) = dpth
depth (ShowLine _ dpth) = dpth
depth (QedLine _ dpth _) = dpth

parseLine :: 
    Parsec String u [r] -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseLine r f = try (parseAssertLine r f) 
                <|> try (parseShowLine f) 
                <|> try (parseQedLine r)

parseAssertLine :: Parsec String u [r] -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseAssertLine r f = do dpth  <- indent
                         phi <- f
                         (rule,deps) <- rline r
                         return $ AssertLine phi rule dpth deps

parseShowLine :: Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseShowLine f = do dpth <- indent
                     string "Show:" <|> string "show:"
                     spaces
                     phi <- f
                     return $ ShowLine phi dpth
 
parseQedLine :: Parsec String u [r] -> Parsec String u (DeductionLine r lex a)
parseQedLine r = do dpth <- indent 
                    (rule, deps) <- rline r
                    return $ QedLine rule dpth deps

--find the prooftree corresponding to *line n* in ded, where proof line numbers start at 1
--TODO: handle a list of deductionlines which contains some parsing errors
toProofTree :: (Inference r lex, Sequentable lex) => [DeductionLine r lex (Form Bool)] -> Int -> Either ProofErrorMessage (ProofTree r lex)
toProofTree ded n = case ded !! (n - 1)  of
          (AssertLine f r dpth deps) -> 
                do mapM checkDep deps
                   deps' <- mapM (\x -> toProofTree ded x) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where checkDep depline = takeRange depline n >>= scan
          (ShowLine f d) -> 
                do m <- matchShow
                   let (QedLine r _ deps) = ded !! m
                   mapM (checkDep $ m + 1) deps 
                   deps' <- mapM (\x -> toProofTree ded x) deps
                   return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'
                where --for scanning, we ignore the depth of the QED line
                      checkDep m m' = takeRange m' m >>= scan . init
                      matchShow = let ded' = drop n ded in
                          case findIndex (qedAt d) ded' of
                              Nothing -> Left "Open subproof (no corresponding QED)"
                              Just m' -> isSubProof n (n + m' - 1)
                      isSubProof n m = let (h:t) = lineRange n m ded in
                          case and (map (\x -> depth x > depth h) t) of
                              False -> Left $ "Open subproof on lines" ++ show n ++ " to " ++ show m ++ " (no QED in this subproof)"
                              True -> Right (m + 1)
                      qedAt d (QedLine _ dpth _) = d == dpth
                      qedAt d _ = False
          (QedLine _ _ _) -> Left "A QED line cannot be cited as a justification" 
    where ln = length ded
          --line h is accessible from the end of the chunk if everything in
          --the chunk has depth greater than or equal to that of line h
          scan chunk@(h:_) =
              if and (map (\x -> depth h <= depth x) chunk)
                  then Right True
                  else Left "It looks like you're citing a line which is not in your subproof. If you're not, you may need to tidy up your proof."
          takeRange m' n' = 
              if n' <= m' 
                      then Left "Dependency is later than assertion"
                      else Right $ lineRange m' n' ded
          --sublist, given by line numbers
          lineRange m n l = drop (m - 1) $ take n l

--------------------------------------------------------
--Utilities
--------------------------------------------------------

parseInts :: Parsec String u [Int]
parseInts = do ints <- many1 digit `sepBy` separator
               return $ map read ints
    where separator = spaces *> optional (string ",") *> spaces 

rline r = do rule <- spaces *> char ':' *> r 
             deps <- spaces *> parseInts
             return (rule, deps)

--need to handle tabs
indent = do ws <- many $ char ' '
            return $ length ws

--------------------------------------------------------
--Testing
--------------------------------------------------------

parsePropLogic :: Parsec String u [PropLogic]
parsePropLogic = do r <- choice (map (try . string) ["AS","PR","MP","MT","DD","DNE","DNI", "DN", "CD", "ID"])
                    case r of
                        "AS"  -> return [AX]
                        "PR"  -> return [AX]
                        "MP"  -> return [MP]
                        "MT"  -> return [MT]
                        "DD"  -> return [DD]
                        "DNE" -> return [DNE]
                        "DNI" -> return [DNI]
                        "DN"  -> return [DNE,DNI]
                        "CD"  -> return [CP1,CP2]
                        "ID"  -> return [ID1,ID2,ID3]

parsePropProof :: String -> [Either ParseError (DeductionLine PropLogic PurePropLexicon (Form Bool))]
parsePropProof = toDeduction parsePropLogic prePurePropFormulaParser

toDisplaySequencePropProof :: String -> 
    (Maybe (ClassicalSequentOver PurePropLexicon Sequent),[Either ProofErrorMessage (ClassicalSequentOver PurePropLexicon Sequent)])
toDisplaySequencePropProof s = if isParsed 
                                   then let feedback = map (processLine(rights ded)) [1 .. length ded] in
                                       (lastTopInd >>= fromFeedback feedback , feedback )
                                   else (Nothing, map handle ded)
    where ded = parsePropProof s
          isParsed = null $ lefts ded 
          handle (Left e) = Left $ "parsing error:" ++ show e
          handle (Right _) = Left ""
          isTop x = case x of
            (Right (AssertLine _ _ 0 _)) -> True
            (Right (ShowLine _ 0)) -> True
            _ -> False
          lastTopInd = do i <- findIndex isTop (reverse ded)
                          return $ length ded - i
          fromFeedback fb n = case fb !! (n - 1) of
            Left _ -> Nothing
            Right s -> Just s
          processLine ded n = case ded !! (n - 1) of
            --special case to catch QedLines not being cited in justifications
            (QedLine _ _ _) -> Left ""
            _ -> toProofTree ded n >>= firstLeft . reduceProofTree
          firstLeft (Left (x:xs)) = Left x
          firstLeft (Right x) = Right x
