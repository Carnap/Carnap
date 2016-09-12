{-#LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser 

where

--import Data.Tree
import Data.Either
import Data.List
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
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
                     string "Show" <|> string "show"
                     optional $ char ':'
                     spaces
                     phi <- f
                     return $ ShowLine phi dpth
 
parseQedLine :: Parsec String u [r] -> Parsec String u (DeductionLine r lex a)
parseQedLine r = do dpth <- indent 
                    (rule, deps) <- rline r
                    return $ QedLine rule dpth deps

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
