{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.Lemmon 
where

import Data.Tree
import Data.Typeable
import Data.List (findIndex)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser

parseDependentAssertLine :: Parsec String u [r] -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseDependentAssertLine r f = do mscope <- optionMaybe scope
                                  let scope = case mscope of Nothing -> []; Just l -> l
                                  spaces
                                  phi <- f
                                  (dis, deps, rule) <- lemline r
                                  return $ DependentAssertLine phi rule (map (\x->(x,x)) deps) dis scope

lemline r = do dis <- scope
               spaces
               deps <- citation `sepBy` spaces
               spaces
               rule <- r
               return (dis,deps,rule)

citation :: Parsec String u Int
citation = char '(' *> (read <$> many1 digit) <* char ')'

scope = char '[' *> parseInts <* char ']'
