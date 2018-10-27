module Carnap.Calculi.NaturalDeduction.Parser.Util where

import Text.Parsec
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Core.Data.Types

--need to handle tabs
indent  :: Parsec String u Int
indent = do ws <- many $ char ' '
            return $ length ws

rline r = do rule <- spaces *> char ':' *> r 
             deps <- spaces *> parseInts
             return (rule, deps)

parseInts :: Parsec String u [Int]
parseInts = do ints <- many1 digit `sepEndBy` separator
               return $ map read ints
    where separator = spaces *> optional (string ",") *> spaces 

parseAssertLine :: Parsec String u [r] -> Parsec String u (FixLang lex a) 
    -> Parsec String u (DeductionLine r lex a)
parseAssertLine r f = do dpth  <- indent
                         phi <- f
                         (rule,deps) <- rline r
                         return $ AssertLine phi rule dpth (map (\x -> (x,x)) deps)

{- Parse a string line-by-line into a deduction -}
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
