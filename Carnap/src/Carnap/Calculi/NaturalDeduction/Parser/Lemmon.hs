{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.Lemmon 
where

import Data.Tree
import Data.Typeable
import Data.List (sort,(\\),nub)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser

parseDependentAssertLine r f j  = do mscope <- optionMaybe scope
                                     let thescope = case mscope of Nothing -> []; Just l -> l
                                     spaces
                                     phi <- f
                                     (dis, deps, rule) <- j r
                                     return $ DependentAssertLine phi rule (map (\x->(x,x)) deps) dis thescope

--lemmon justifications as given in Goldfarb
lemline r = do mdis <- optionMaybe scope
               let dis = case mdis of Nothing -> []; Just l -> l
               spaces
               deps <- citation `sepEndBy` spaces
               annote <- many (noneOf (' ':['A' .. 'Z']))
               spaces
               rule <- r (length deps) annote
               return (dis,deps,rule)

--lemmon justifications as used at Brown
lemlineAlt r = do (dis,deps,annote) <- lookAhead $ 
                    do many (oneOf ['A' .. 'Z'])
                       (mdis,mdeps,annote) <- try cite1 <|> try cite2 <|> cite3
                       let deps = case mdeps of Nothing -> []; Just l -> l
                       let dis = case mdis of Nothing -> []; Just l -> l
                       return (dis,deps,annote)
                  rule <- r (length deps) annote
                  return (dis,deps,rule)
    where cite1 = (,,) <$> (Just <$> scope) <*> (Just <$> bothCitations) <*> annotation
          cite2 = (\x y z -> (y,x,z)) <$> (Just <$> bothCitations) <*> (Just <$> scope) <*> annotation
          cite3 = (,,) <$> optionMaybe scope <*> optionMaybe bothCitations <*> annotation
          bothCitations = try (citation `sepEndBy` spaces) <|> citations

citation :: Parsec String u Int
citation = char '(' *> (read <$> many1 digit) <* char ')'

citations :: Parsec String u [Int]
citations = char '(' *> ((read <$> many1 digit)`sepBy` (char ',' >> spaces)) <* char ')'

annotation :: Parsec String u String
annotation = many (noneOf (' ':['A' .. 'Z']))

scope = char '[' *> parseInts <* char ']'

toDeductionLemmon :: (Int -> String -> Parsec String () [r]) -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionLemmon r f = toDeduction (parseDependentAssertLine r f lemline)

toDeductionLemmonAlt :: (Int -> String -> Parsec String () [r]) -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionLemmonAlt r f = toDeduction (parseDependentAssertLine r f lemlineAlt)

toProofTreeLemmon :: 
    ( Inference r lex sem
    , Sequentable lex
    , Typeable sem
    ) => Deduction r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeLemmon ded n = case ded !! (n - 1) of
    (DependentAssertLine f r depairs dis scope) ->
        do let deps = map fst depairs
           mapM_ checkDep deps
           let inherited = concat $ map (\m -> inScope (ded !! (m - 1))) deps
           checkScope inherited
           deps' <- mapM (toProofTreeLemmon ded) (deps ++ dis)
           return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'

        where err :: String -> Either (ProofErrorMessage lex) a
              err x = Left $ GenericError x n

              checkDep m | n <= m = err $ "line " ++ show m ++ " is being cited, but is later than this assertion."
                         | otherwise = Right True

              checkScope i | isAssumption (head r) && not (scope == i ++ [n]) = err "The dependencies here aren't right. Remember, this rule introduces its own line number as a dependency."
                           | isAssumption (head r) = if dis /= [] then err "This rule does not allow the elimination of dependencies." else Right True
                           | null (globalRestriction (Left []) 0 (head r)) && dis /= [] = err "This rule does not allow the elimination of dependencies."
                           | sort scope /= sort (nub i \\ dis) = err "The dependencies here aren't right. Did you forget mark a dependency as eliminated?."
                           | otherwise = Right True

    (PartialLine _ e _) -> Left $ NoParse e n
