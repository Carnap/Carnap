{-#LANGUAGE FlexibleContexts #-}
module Carnap.Calculi.NaturalDeduction.Parser.Lemmon 
where

import Data.Tree
import Data.Typeable
import Data.List (sort,(\\),nub)
import Text.Parsec
import Carnap.Core.Data.Types
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser.Util
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser

parseDependentAssertLine withNum r f j  = do mscope <- optionMaybe scope
                                             let thescope = case mscope of Nothing -> []; Just l -> l
                                             spaces
                                             mnum <- if withNum 
                                                        then (char '(' *> (Just . read <$> many1 digit) <* char ')') 
                                                             <|> ((Just . read <$> many1 digit) <* char '.')
                                                             <?> "line number"
                                                        else return Nothing
                                             spaces
                                             phi <- f
                                             (dis, deps, rule) <- j r
                                             return $ DependentAssertLine phi rule (map (\x->(x,x)) deps) dis thescope mnum

parseDependentAssertLineWithNum = parseDependentAssertLine True

parseDependentAssertLinePlain = parseDependentAssertLine False

--lemmon justifications as given in Goldfarb
lemline r = do mdis <- optionMaybe scope
               let dis = case mdis of Nothing -> Just []; l -> l
               spaces
               deps <- citation `sepEndBy` spaces
               annote <- annotation
               spaces
               rule <- r (length deps) annote
               return (dis,deps,rule)

--lemmon justifications as used at Brown
lemlineAlt r = do (dis,deps,annote) <- lookAhead $ 
                    do many (oneOf ['A' .. 'Z'])
                       (mdis,mdeps,annote) <- try cite1 <|> try cite2 <|> cite3
                       let deps = case mdeps of Nothing -> []; Just l -> l
                       let dis = case mdis of Nothing -> Just []; l -> l
                       return (dis,deps,annote)
                  rule <- r (length deps) annote
                  return (dis,deps,rule)
    where cite1 = (,,) <$> (Just <$> scope) <*> (Just <$> bothCitations) <*> annotation
          cite2 = (\x y z -> (y,x,z)) <$> (Just <$> bothCitations) <*> (Just <$> scope) <*> annotation
          cite3 = (,,) <$> optionMaybe scope <*> optionMaybe bothCitations <*> annotation
          bothCitations = try (citation `sepEndBy` spaces) <|> citations


lemlineImplicit r = do indicated <- parseInts
                       spaces
                       rule <- r 0 ""
                       --XXX: discharge of assumptions is done implicitly,
                       --rather than explicitly flagged in this system.
                       --Hence "Nothing" is discharged
                       return (Nothing,indicated,rule)

citation :: Parsec String u Int
citation = char '(' *> (read <$> many1 digit) <* char ')'

citations :: Parsec String u [Int]
citations = char '(' *> ((read <$> many1 digit)`sepBy` (char ',' >> spaces)) <* char ')'

annotation :: Parsec String u String
annotation = many (oneOf ['a' .. 'z'])

scope = (char '[' *> parseInts <* char ']') <|> (char '{' *> parseInts <* char '}')

toDeductionLemmon :: (Int -> String -> Parsec String () [r]) -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionLemmon r f = toDeduction (parseDependentAssertLinePlain r f lemline)

toDeductionLemmonAlt :: (Int -> String -> Parsec String () [r]) -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionLemmonAlt r f = toDeduction (parseDependentAssertLinePlain r f lemlineAlt)

toDeductionLemmonTomassi :: Inference r lex (Form Bool) => (Int -> String -> Parsec String () [r]) -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionLemmonTomassi r f = toDeduction (parseDependentAssertLineWithNum r f lemlineImplicit)

toDeductionLemmonImplicit :: Inference r lex (Form Bool) => (Int -> String -> Parsec String () [r]) -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionLemmonImplicit r f = toDeduction (parseDependentAssertLinePlain r f lemlineImplicit)

toProofTreeLemmon :: 
    ( Inference r lex sem
    , Sequentable lex
    , Typeable sem
    ) => Deduction r lex sem -> Int -> Either (ProofErrorMessage lex) (ProofTree r lex sem)
toProofTreeLemmon ded n = case ded !! (n - 1) of
    l@(DependentAssertLine f r depairs mdis scope mnum) ->
        do let deps = map fst depairs
           mapM_ checkDep deps
           checkNum mnum
           let inherited = concat $ map (\m -> inScope (ded !! (m - 1))) deps
           checkScope inherited
           deps' <- mapM (toProofTreeLemmon ded) (deps ++ discharged l)
           return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'

        where err :: String -> Either (ProofErrorMessage lex) a
              err x = Left $ GenericError x n

              checkDep m | n <= m = err $ "line " ++ show m ++ " is being cited, but is later than this assertion."
                         | otherwise = Right True

              checkScope i | isAssumption (head r) && not (scope == i ++ [n]) = err "The dependencies here aren't right. Remember, this rule introduces its own line number as a dependency."
                           | isAssumption (head r) = if nodis then Right True else err "This rule does not allow the elimination of dependencies."
                           | null (globalRestriction (Left []) 0 (head r)) && not nodis = err "This rule does not allow the elimination of dependencies."
                           | length (nub i) - numDischarged (indirectInference (head r)) /= length scope = err "This is the wrong number of dependencies. Did you forget to add or remove something?"
                           | mdis /= Nothing && sort scope /= sort (nub i \\ discharged l) = err "The dependencies here aren't right. Did you forget mark a dependency as eliminated?."
                           | otherwise = Right True

              nodis = discharged l == []

              numDischarged (Just (TypedProof (ProofType n _ ))) = n
              numDischarged (Just (PolyTypedProof m (ProofType n _))) = m * n
              numDischarged _ = 0

              checkNum Nothing = return ()
              checkNum (Just m) = if m == n then return () else err "This line is numbered incorrectly"

    (PartialLine _ e _) -> Left $ NoParse e n
