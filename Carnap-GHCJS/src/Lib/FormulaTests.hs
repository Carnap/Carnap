{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}
module Lib.FormulaTests where

import Carnap.Core.Data.Types (FixLang, Form, Term, BoundVars, FirstOrderLex)
import Carnap.Languages.Util.LanguageClasses
import Control.Lens (Prism', toListOf, cosmos, Fold, filtered)
import Carnap.Languages.PurePropositional.Util (isDNF, isCNF, HasLiterals(..))
import Carnap.Core.Data.Optics (genChildren, PrismSubstitutionalVariable)
import Carnap.Languages.PureFirstOrder.Util (isPNF)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)

type BinaryTest lex sem = FixLang lex sem -> FixLang lex sem -> Bool

type UnaryTest lex sem = FixLang lex sem -> Maybe String

folTests :: forall lex . 
     ( HasLiterals lex Bool
     , PrismGenericQuant lex Term Form Bool Int
     , PrismBooleanConst lex Bool
     , PrismSubstitutionalVariable lex
     , BoundVars lex
     , FirstOrderLex (lex (FixLang lex))
     )=> [String] -> UnaryTest lex (Form Bool)
folTests testlist f = case catMaybes $ map ($ f) theTests of 
                            [] -> Nothing
                            s:ss -> Just $ foldl (\x y -> x ++ ", and " ++ y) s ss
    where theTests = map toTest testlist ++ [propTests testlist]
          toTest "PNF" submission | isPNF submission = Nothing
                                  | otherwise = Just "this submission is not in Prenex Normal Form"
          toTest _ _ = Nothing

propTests :: forall sem lex . 
    ( PrismBooleanConnLex lex sem
    , PrismBooleanConst lex sem
    , HasLiterals lex sem
    , BoundVars lex
    ) => [String] -> UnaryTest lex (Form sem)
propTests testlist f = case catMaybes $ map ($ f) theTests of 
                            [] -> Nothing
                            s:ss -> Just $ foldl (\x y -> x ++ ", and " ++ y) s ss
    where theTests = map toTest testlist
          toTest "CNF" submission | isCNF submission = Nothing
                                  | otherwise = Just "this submission is not in Conjunctive Normal Form"
          toTest "DNF" submission | isDNF submission = Nothing
                                  | otherwise = Just "this submission is not in Disjunctive Normal Form"
          toTest max submission   | take 7 max == "maxNeg:"   = maxWith 7 max (retype _not') "negations" submission
                                  | take 7 max == "maxAnd:"   = maxWith 7 max (retype _and') "conjunctions" submission
                                  | take 7 max == "maxIff:"   = maxWith 7 max (retype _iff') "biconditionals" submission
                                  | take 6 max == "maxIf:"    = maxWith 6 max (retype _if') "conditionals" submission
                                  | take 6 max == "maxOr:"    = maxWith 6 max (retype _or') "disjunctions" submission
                                  | take 7 max == "maxCon:"   = maxWith 7 max (cosmos . _nonAtom) "connectives" submission
                                  | take 8 max == "maxAtom:"  = maxWith 8 max (cosmos . _atom) "atomic sentences" submission
                                  | take 9 max == "maxFalse:" = maxWith 9 max (cosmos . _falsum) "falsity constants" submission
          toTest _ _ = Nothing

          countFold p = length . toListOf p
          retype p = genChildren . cosmos . p

          maxWith len tag p label submission = 
                do n <- readMaybe (drop len tag)
                   let occurs = countFold p submission
                   if occurs > n 
                   then Just $ "you have " ++ show occurs ++ " " ++ label ++ ", but should have "
                             ++ show n ++ " at most"
                   else Nothing

          _nonAtom :: Fold (FixLang lex (Form sem)) (FixLang lex (Form sem))
          _nonAtom = filtered (not . isAtom)

          _not' :: Prism' (FixLang lex (Form sem -> Form sem)) ()
          _not' = _not

          _atom :: Fold (FixLang lex (Form sem)) (FixLang lex (Form sem))
          _atom = filtered isAtom

          _if' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _if' = _if

          _or' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _or' = _or

          _iff' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _iff' = _iff 

          _and' :: Prism' (FixLang lex (Form sem -> Form sem -> Form sem)) ()
          _and' = _and 
