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

parseIt s = case parse purePropFormulaParser "" s of
              Right form -> SS $ liftToSequent form
              _ -> error "boo"

demoTree :: ProofTree PropLogic PurePropLexicon
demoTree = Node (ProofLine 0 (parseIt "P_1") MP)
                [ Node (ProofLine 0 (parseIt "P_2 -> P_1") MP)
                    [ Node (ProofLine 0 (parseIt "P_3 -> (P_2 -> P_1)") AX) []
                    , Node (ProofLine 0 (parseIt "P_3") AX) []
                    ]
                , Node (ProofLine 0 (parseIt "P_2") AX) [] 
                ]

demoPropProof = "P_1 :AX\nP_1 -> P_2 :AX\nP_2 :MP 1,2\nShow: P_2\n  P_3 :AX\n:MP 1,2"

toDeduction :: Parsec String () r -> Parsec String () (FixLang lex a) -> String 
    -> [Either ParseError (DeductionLine r lex a)]
toDeduction r f = map (parse (parseLine r f) "") . lines

data DeductionLine r lex a where
        AssertLine :: 
            { asserted :: FixLang lex a
            , assertRule :: r
            , assertDepth :: Int
            , assertDependencies :: [Int]
            } -> DeductionLine r lex a
        ShowLine :: 
            { toShow :: FixLang lex a
            , showDepth :: Int
            } -> DeductionLine r lex a
        QedLine :: 
            { closureRule :: r
            , closureDepth :: Int
            , closureDependencies :: [Int]
            } -> DeductionLine r lex a

depth (AssertLine _ _ dpth _) = dpth
depth (ShowLine _ dpth) = dpth
depth (QedLine _ dpth _) = dpth

parseLine :: 
    Parsec String u r -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseLine r f = try (parseAssertLine r f) 
                <|> try (parseShowLine f) 
                <|> try (parseQedLine r)

parseAssertLine :: Parsec String u r -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
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
 
parseQedLine :: Parsec String u r -> Parsec String u (DeductionLine r lex a)
parseQedLine r = do dpth <- indent 
                    (rule, deps) <- rline r
                    return $ QedLine rule dpth deps

--find the prooftree corresponding to *line n* in ded, where proof line numbers start at 1
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
                where checkDep m m' = takeRange m' m >>= scan 
                      matchShow = let ded' = drop n ded in
                          case findIndex (qedAt d) ded' of
                              Nothing -> Left "Open subproof (no corresponding QED)"
                              Just m' -> isSubProof n (n + m' - 1)
                      isSubProof n m = let (h:t) = lineRange n m ded in
                          case and (map (\x -> depth x < depth h) t) of
                              False -> Left "Open subproof (no QED in this subproof)"
                              True -> Right (m + 1)
                      qedAt d (QedLine _ dpth _) = d == dpth
                      qedAt d _ = False
          (QedLine _ _ _) -> Left "A QED line cannot be cited as a justification" 
    where ln = length ded
          scan chunk@(h:_) =
              if and (map (\x -> depth h <= depth x) chunk)
                  then Right True
                  else Left $ "head has depth" ++ (show $ depth h)
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
parseInts = do ints <- sepBy (many1 digit) (string ",")
               return $ map read ints

rline r = do rule <- spaces *> char ':' *> r 
             deps <- spaces *> parseInts
             return (rule, deps)

--need to handle tabs
indent = do ws <- many $ char ' '
            return $ length ws

parsePropLogic :: Parsec String u PropLogic
parsePropLogic = do r <- string "AX" <|> string "MP"
                    case r of
                        "AX" -> return AX
                        "MP" -> return MP

parsePropProof :: String -> [Either ParseError (DeductionLine PropLogic PurePropLexicon (Form Bool))]
parsePropProof = toDeduction parsePropLogic prePurePropFormulaParser
