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

parseDependentAssertLine :: (Int -> Parsec String u [r]) -> Parsec String u (FixLang lex a) -> Parsec String u (DeductionLine r lex a)
parseDependentAssertLine r f = do mscope <- optionMaybe scope
                                  let thescope = case mscope of Nothing -> []; Just l -> l
                                  spaces
                                  phi <- f
                                  (dis, deps, rule) <- lemline r
                                  return $ DependentAssertLine phi rule (map (\x->(x,x)) deps) dis thescope

lemline r = do mdis <- optionMaybe scope
               let dis = case mdis of Nothing -> []; Just l -> l
               spaces
               deps <- citation `sepEndBy` spaces
               rule <- r (length deps)
               return (dis,deps,rule)

citation :: Parsec String u Int
citation = char '(' *> (read <$> many1 digit) <* char ')'

scope = char '[' *> parseInts <* char ']'

toDeductionLemmon :: (Int -> Parsec String () [r]) -> Parsec String () (FixLang lex a) -> String 
    -> Deduction r lex a
toDeductionLemmon r f = toDeduction (parseDependentAssertLine r f)

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
           deps' <- mapM (toProofTreeLemmon ded) deps
           return $ Node (ProofLine n (SS $ liftToSequent f) r) deps'

        where err :: String -> Either (ProofErrorMessage lex) a
              err x = Left $ GenericError x n

              checkDep m | n <= m = err $ "dependency on line " ++ show m ++ " is later than assertion."
                         | otherwise = Right True

              checkScope i | isAssumption (head r) = if not (scope == [n]) then err "Premises introduce exactly their own line numbers as dependencies." else Right True
                           | sort scope /= sort (nub i \\ dis) = err "There's a mismatch between the stated premises and the undischarged premises inherited from previous lines."
                           | otherwise = Right True

    (PartialLine _ e _) -> Left $ NoParse e n
