{-#LANGUAGE GADTs, FlexibleContexts, RankNTypes, PatternSynonyms,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Rules where

import Text.Parsec
import Data.List
import Data.Maybe (catMaybes)
import Control.Lens (toListOf, view)
import Carnap.Calculi.NaturalDeduction.Syntax
import Data.Typeable
import Carnap.Core.Unification.Unification
import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Types
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConstructors

--------------------------------------------------------
--1 Propositional Sequent Calculus
--------------------------------------------------------

type PropSequentCalc = ClassicalSequentOver PurePropLexicon

type PropSequentCalcLex = ClassicalSequentLexOver PurePropLexicon

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema PropSequentCalc

data PropSeqLabel = PropSeqFO | PropSeqACUI
        deriving (Eq, Ord, Show)

instance Eq (PropSequentCalc a) where
        (==) = (=*)

premConstraint Nothing _ = Nothing
premConstraint (Just prems) sub | theinstance `elem` prems = Nothing
                                | otherwise = Just (show (project theinstance) ++ " is not one of the premises " 
                                                                               ++ intercalate ", " (map (show . project) prems))
    where theinstance = betaNormalizeByName $ applySub sub $ (SA (phin 1) :|-: SS (phin 1))
          project = view rhs

dischargeConstraint n ded lhs sub | all (`elem` lhs') forms = Nothing
                                  | otherwise = Just $ "Some of the stated dependencies in " ++ show forms ++ ", are not among the inferred dependencies " ++ show lhs' ++  "."
    where lhs' = toListOf concretes . applySub sub $ lhs
          scope = inScope (ded !! (n - 1))
          forms = catMaybes . map (\n -> liftToSequent <$> assertion (ded !! (n - 1))) $ scope

fitchAssumptionCheck n ded pairs sub = checkWithProofType n ded pairs sub theProoftype
    where checkWithProofType n ded pairs sub (WithAlternate a1 a2) = checkWithProofType n ded pairs sub a1 >> checkWithProofType n ded pairs sub a2
          checkWithProofType n ded pairs sub pt | not (all (`among` pairs') allBoundaryAssertions) = Just $ "Some of the assumptions in the cited subproofs are not of the right form for this rule."
                                                | not (all (`among` allBoundaryAssertions) pairs') = Just $ "Some of the assumptions this rule requires you to make are missing from the boundary conditions."
                                                | otherwise = Nothing
                where subproofBoundries = case pt of
                         --pending further refinement to the ProofType
                         --system, we ignore t, since this indicates how
                         --many assumptions are actually used in generating
                         --the unification problem, and that may differ
                         --from the number of assumptions (AFAIK, always 1)
                         --that are present in a fitch subproof. If that
                         --turns out to be false, then probably another
                         --prooftype is appropriate, and would feed
                         --something other than 1 into fromBoundary
                         (ImplicitProof (ProofType t b)) -> [fromBoundary 1 b (n - (length precedingProof), n - 1)]
                         (TypedProof (ProofType t b)) -> maybe (error "assumption check on non-assertion") (map (fromBoundary 1 b) . checkDistinct) $ dependencies callingLine
                         (PolyTypedProof _ (ProofType t b)) -> maybe (error "assumption check on non-assertion") (map (fromBoundary 1 b) . checkDistinct) $ dependencies callingLine
                         PolyProof -> maybe (error "assumption check on non-assertion") (map (fromBoundary 1 1) . checkDistinct) $ dependencies callingLine
                      allBoundaryAssertions = map (\(p,q) -> (map liftToSequent p, map liftToSequent q)) $ catMaybes $ map boundaryAssertions subproofBoundries
          checkDistinct = filter (\(i,j) -> i /= j)
          fromBoundary t b (t',b') = (take t [t' ..], take b [b', b' -1 ..])
          callingLine = ded !! (n - 1)
          boundaryAssertions (l1,l2) = (,) <$> mapM assertionAt l1 <*> mapM assertionAt l2
          boundaryAssertions _ = Nothing
          assertionAt n = assertion (ded !! (n - 1))
          pairs' = map (\(p,q) -> (map (pureBNF . applySub sub) p, map (pureBNF . applySub sub) q)) pairs
          precedingProof = takeWhile (\x -> depth x > depth (ded !! (n - 1))) . reverse . take (n - 1) $ ded
          --XXX: the below is sort of inelegant, since it is not going to
          --allow the possibility of one "rule" having more than one
          --assocated prooftype. This is sort of a consequence of the
          --prior inelegance of not parsing to prooftrees
          --indeterministically
          theProoftype = maybe (error "no indirect calling rule") id ((head <$> ruleOfLine callingLine) >>= indirectInference)
          setEq x y = all (`elem` x) y && all (`elem` y) x
          pairEq (a,b) (c,d) = a `setEq` c && b `setEq` d
          among x (y:ys) = x `pairEq` y || x `among` ys
          among x [] = False

-------------------------
--  1.1 Standard Rules  --
-------------------------
--Rules found in many systems of propositional logic

type BooleanRule lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        ) => SequentRule lex (Form b)

modusPonens :: BooleanRule lex b
modusPonens = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
              , GammaV 2 :|-: SS (phin 1)
              ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)

modusTollens :: BooleanRule lex b
modusTollens = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
               , GammaV 2 :|-: SS (lneg $ phin 2)
               ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)

axiom :: BooleanRule lex b
axiom = [] ∴ SA (phin 1) :|-: SS (phin 1)

explosion :: Int -> BooleanRule lex b
explosion n = map (\m -> GammaV m :|-: SS (phin m)) [1 .. n]
              ∴ concAnt :|-: SS (phin (n + 1))
    where concAnt = foldr (:+:) Top (map GammaV [1 .. n])

exfalso :: BooleanRule lex b
exfalso = [ GammaV 1 :|-: SS (phin 1)
          , GammaV 2 :|-: SS (lneg $ phin 1)
          ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)

identityRule :: BooleanRule lex b
identityRule = [ GammaV 1 :|-: SS (phin 1) 
               ] ∴ GammaV 1 :|-: SS (phin 1)

doubleNegationElimination :: BooleanRule lex b
doubleNegationElimination = [ GammaV 1 :|-: SS (lneg $ lneg $ phin 1) 
                            ] ∴ GammaV 1 :|-: SS (phin 1) 

doubleNegationIntroduction :: BooleanRule lex b
doubleNegationIntroduction = [ GammaV 1 :|-: SS (phin 1) 
                             ] ∴ GammaV 1 :|-: SS (lneg $ lneg $ phin 1) 

falsumElimination :: BooleanRule lex b
falsumElimination = [ GammaV 1 :|-: SS lfalsum
                    ] ∴ GammaV 1 :|-: SS (phin 1)

falsumIntroduction :: BooleanRule lex b
falsumIntroduction = [ GammaV 1 :|-: SS (lneg $ phin 1)
                     , GammaV 2 :|-: SS (phin 1)
                     ] ∴ GammaV 1 :+: GammaV 2 :|-: SS lfalsum

adjunction :: BooleanRule lex b
adjunction = [ GammaV 1  :|-: SS (phin 1) 
             , GammaV 2  :|-: SS (phin 2)
             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1 .∧. phin 2)

conditionalToBiconditional :: BooleanRule lex b
conditionalToBiconditional = [ GammaV 1  :|-: SS (phin 1 .→. phin 2)
                             , GammaV 2  :|-: SS (phin 2 .→. phin 1) 
                             ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1 .↔. phin 2)

biconditionalToTwoConditional :: BooleanRule lex b
biconditionalToTwoConditional = [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                                ] ∴ GammaV 1 :|-: SS ((phin 1 .→. phin 2) .∧. (phin 2 .→. phin 1))

dilemma :: BooleanRule lex b
dilemma = [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
          , GammaV 2 :|-: SS (phin 1 .→. phin 3)
          , GammaV 3 :|-: SS (phin 2 .→. phin 3)
          ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)

constructiveDilemma :: BooleanRule lex b
constructiveDilemma = [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
          , GammaV 2 :|-: SS (phin 1 .→. phin 3)
          , GammaV 3 :|-: SS (phin 2 .→. phin 4)
          ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3 .∨. phin 4)

conjunctionDilemma :: BooleanRule lex b
conjunctionDilemma = [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
                     , GammaV 2 :|-: SS ((phin 1 .→. phin 3) .∧. (phin 2 .→. phin 3))
                     ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 3)

hypotheticalSyllogism :: BooleanRule lex b
hypotheticalSyllogism = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
                        , GammaV 2 :|-: SS (phin 2 .→. phin 3)
                        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1 .→. phin 3)

proofByCases :: BooleanRule lex b
proofByCases = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
               , GammaV 2 :|-: SS ((lneg $ phin 1) .→. phin 2)
               ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)

conditionalReductio :: BooleanRule lex b 
conditionalReductio = [ GammaV 1 :|-: SS (phin 1 .→. phin 2)
               , GammaV 2 :|-: SS (phin 1 .→. (lneg $ phin 2))
               ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)

---------------------------
--  1.2 Variation Rules  --
---------------------------
-- Rules with several variations

type BooleanRuleVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        ) => [SequentRule lex (Form b)]

------------------------------
--  1.2.1 Simple Variation  --
------------------------------

doubleNegatingModusTollensVariations :: BooleanRuleVariants lex b
doubleNegatingModusTollensVariations = [
        [ GammaV 1 :|-: SS (lneg (phin 1) .→. lneg (phin 2))
        , GammaV 2 :|-: SS (phin 2)
        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
    ,
        [ GammaV 1 :|-: SS (phin 1 .→. lneg (phin 2))
        , GammaV 2 :|-: SS (phin 2)
        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
    ,
        [ GammaV 1 :|-: SS (lneg (phin 1) .→. phin 2)
        , GammaV 2 :|-: SS (lneg $ phin 2)
        ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
    ]

modusTollendoPonensVariations :: BooleanRuleVariants lex b
modusTollendoPonensVariations = [
                [ GammaV 1  :|-: SS (lneg $ phin 1) 
                , GammaV 2  :|-: SS (phin 1 .∨. phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            , 
                [ GammaV 1  :|-: SS (lneg $ phin 1) 
                , GammaV 2  :|-: SS (phin 2 .∨. phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ]

doubleNegatingModusTollendoPonensVariations :: BooleanRuleVariants lex b
doubleNegatingModusTollendoPonensVariations = [
                [ GammaV 1  :|-: SS (phin 1) 
                , GammaV 2  :|-: SS ((lneg $ phin 1) .∨. phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            , 
                [ GammaV 1  :|-: SS (phin 1) 
                , GammaV 2  :|-: SS (phin 2 .∨. (lneg $ phin 1))
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ]

constructiveReductioVariations :: BooleanRuleVariants lex b
constructiveReductioVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                , GammaV 2 :+: SA (phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,

                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                , GammaV 2 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,

                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2 :+: SA (phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2  :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ]

explicitConstructiveReductioVariations :: BooleanRuleVariants lex b
explicitConstructiveReductioVariations = [
                [ SA (phin 1) :|-: SS (phin 1)
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                , GammaV 2 :+: SA (phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,

                [ SA (phin 1) :|-: SS (phin 1)
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                , GammaV 2 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1)
                , GammaV 1  :|-: SS (phin 2) 
                , GammaV 2 :+: SA (phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1)
                , GammaV 1  :|-: SS (phin 2) 
                , GammaV 2  :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ]

nonConstructiveReductioVariations :: BooleanRuleVariants lex b
nonConstructiveReductioVariations = [
                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS (phin 2) 
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ,

                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS (phin 2) 
                , GammaV 2 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ,

                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 2) 
                , GammaV 2  :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS ( phin 1)
            ]

explicitNonConstructiveReductioVariations :: BooleanRuleVariants lex b
explicitNonConstructiveReductioVariations = [
                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :+: SA (lneg $ phin 1) :|-: SS (phin 2) 
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ,

                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :+: SA (lneg $ phin 1) :|-: SS (phin 2) 
                , GammaV 2 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ,
                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1  :|-: SS (phin 2) 
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ,
                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1  :|-: SS (phin 2) 
                , GammaV 2  :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ]

constructiveFalsumReductioVariations :: BooleanRuleVariants lex b
constructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS lfalsum
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ]

--A small hack. Add some junk premises, so that you can combine the falsum
--reductio with a standard reduction under one proof arity.
constructiveFalsumReductioVariationsWithJunk :: BooleanRuleVariants lex b
constructiveFalsumReductioVariationsWithJunk = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS lfalsum
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ]

constructiveConjunctionReductioVariations :: BooleanRuleVariants lex b
constructiveConjunctionReductioVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :+: SA (phin 1) :|-: SS ((lneg $ phin 2) .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :|-: SS ((lneg $ phin 2) .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ]

nonConstructiveFalsumReductioVariations :: BooleanRuleVariants lex b
nonConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS lfalsum
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ]

--A small hack. Add some junk premises, so that you can combine the falsum
--reductio with a standard reduction under one proof arity.
nonConstructiveFalsumReductioVariationsWithJunk :: BooleanRuleVariants lex b
nonConstructiveFalsumReductioVariationsWithJunk = [
                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS lfalsum
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ]

explictConstructiveConjunctionReductioVariations :: BooleanRuleVariants lex b
explictConstructiveConjunctionReductioVariations = [
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :+: SA (phin 1) :|-: SS ((lneg $ phin 2) .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ SA (phin 1) :|-: SS (phin 1) 
                , GammaV 1 :|-: SS ((lneg $ phin 2) .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ]

explictNonConstructiveConjunctionReductioVariations :: BooleanRuleVariants lex b
explictNonConstructiveConjunctionReductioVariations = [
                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1) 
                , GammaV 1 :+: SA (lneg $ phin 1) :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ SA (lneg $ phin 1) :|-: SS (lneg $ phin 1) 
                , GammaV 1 :|-: SS (phin 2 .∧. (lneg $ phin 2))
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ]

explicitConstructiveFalsumReductioVariations :: BooleanRuleVariants lex b
explicitConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS lfalsum
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ]

explicitNonConstructiveFalsumReductioVariations :: BooleanRuleVariants lex b
explicitNonConstructiveFalsumReductioVariations = [
                [ GammaV 1 :+: SA (lneg $ phin 1) :|-: SS lfalsum
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ GammaV 1 :|-: SS lfalsum
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1)
            ]

conditionalProofVariations :: BooleanRuleVariants lex b
conditionalProofVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2) 
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2) 
            ,   [ GammaV 1 :|-: SS (phin 2) 
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2)
            ]

explicitConditionalProofVariations :: BooleanRuleVariants lex b
explicitConditionalProofVariations = [
                [ GammaV 1 :+: SA (phin 1)  :|-: SS (phin 2) 
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2) 
            ,   [ GammaV 1 :|-: SS (phin 2) 
                , SA (phin 1) :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2)
            ]

simplificationVariations :: BooleanRuleVariants lex b
simplificationVariations = [
                [ GammaV 1  :|-: SS (phin 1 .∧. phin 2) ] ∴ GammaV 1 :|-: SS (phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 1 .∧. phin 2) ] ∴ GammaV 1 :|-: SS (phin 2)
            ]

additionVariations :: BooleanRuleVariants lex b
additionVariations = [
                [ GammaV 1  :|-: SS (phin 1) ] ∴ GammaV 1 :|-: SS (phin 2 .∨. phin 1)
            ,
                [ GammaV 1  :|-: SS (phin 1) ] ∴ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
            ]

biconditionalToConditionalVariations :: BooleanRuleVariants lex b
biconditionalToConditionalVariations = [
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2) ] ∴ GammaV 1 :|-: SS (phin 2 .→. phin 1)
            , 
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2) ] ∴ GammaV 1 :|-: SS (phin 1 .→. phin 2)
            ]

proofByCasesVariations :: BooleanRuleVariants lex b
proofByCasesVariations = [
                [ GammaV 1  :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :+: SA (phin 1) :|-: SS (phin 3)
                , GammaV 3 :+: SA (phin 2) :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            ,   
                [ GammaV 1  :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :|-: SS (phin 3)
                , GammaV 3 :+: SA (phin 2) :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            ,   
                [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :+: SA (phin 1) :|-: SS (phin 3)
                , GammaV 3 :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            , 
                [ GammaV 1 :|-: SS (phin 1 .∨. phin 2)
                , GammaV 2 :|-: SS (phin 3)
                , GammaV 3 :|-: SS (phin 3)
                ] ∴ GammaV 1 :+: GammaV 2 :+: GammaV 3 :|-: SS (phin 3)
            ]

tertiumNonDaturVariations :: BooleanRuleVariants lex b
tertiumNonDaturVariations = [
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ,   
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :+: SA (lneg $ phin 1) :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ,   
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            , 
                [ SA (phin 1) :|-: SS (phin 1)
                , SA (lneg $ phin 1) :|-: SS (lneg $ phin 1)
                , GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ]

biconditionalProofVariations :: BooleanRuleVariants lex b
biconditionalProofVariations = [
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :+: SA (phin 2) :|-: SS (phin 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            ,
                [ GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :+: SA (phin 2) :|-: SS (phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            ,
                [ GammaV 1 :+: SA (phin 1) :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            , 
                [ GammaV 1 :|-: SS (phin 2)
                , GammaV 2 :|-: SS (phin 1) 
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2 .↔. phin 1)
            ]

biconditionalPonensVariations :: BooleanRuleVariants lex b
biconditionalPonensVariations = [
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2  :|-: SS (phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 2)
            ,
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2  :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (phin 1)
            ]

biconditionalTollensVariations :: BooleanRuleVariants lex b
biconditionalTollensVariations = [
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2  :|-: SS (lneg $ phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 2)
            ,
                [ GammaV 1  :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2  :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ]

materialConditionalVariations :: BooleanRuleVariants lex b
materialConditionalVariations =  [
                [ GammaV 1 :|-: SS (phin 1)
                ] ∴ GammaV 1 :|-: SS (phin 2 .→. phin 1)
            ,
                [ GammaV 1 :|-: SS (lneg $ phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 2 .→. phin 1)
            ]

negatedConditionalVariations :: BooleanRuleVariants lex b
negatedConditionalVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .→. phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 1 .∧. lneg (phin 2))
            ,
                [ GammaV 1 :|-: SS (phin 1 .∧. lneg (phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .→. phin 2)
            ]

negatedConjunctionVariations :: BooleanRuleVariants lex b
negatedConjunctionVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∧. phin 2)
                ] ∴ GammaV 1 :|-: SS (phin 1 .→. lneg (phin 2))
            ,
                [ GammaV 1 :|-: SS (phin 1 .→. lneg (phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .∧. phin 2)
            ]
            
negatedDisjunctionVariations :: BooleanRuleVariants lex b
negatedDisjunctionVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∨. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1)
            ,
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∨. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 2)
            ]

negatedBiconditionalVariations :: BooleanRuleVariants lex b
negatedBiconditionalVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .↔. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg (phin 1) .↔. phin 2)
            ,
                [ GammaV 1 :|-: SS (lneg (phin 1) .↔. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .↔. phin 2)
            ]

deMorgansNegatedOr :: BooleanRuleVariants lex b
deMorgansNegatedOr = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∨. phin 2)
                ] ∴ GammaV 1 :|-: SS (lneg (phin 1) .∧. lneg (phin 2))
            ,
                [ GammaV 1 :|-: SS (lneg (phin 1) .∧. lneg (phin 2))
                ] ∴ GammaV 1 :|-: SS (lneg $ phin 1 .∨. phin 2)
            ]

conjunctiveSyllogismVariations :: BooleanRuleVariants lex b
conjunctiveSyllogismVariations = [
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∧. phin 2)
                , GammaV 2 :|-: SS (phin 1)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 2)
            ,
                [ GammaV 1 :|-: SS (lneg $ phin 1 .∧. phin 2)
                , GammaV 2 :|-: SS (phin 2)
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lneg $ phin 1)
            ]
-------------------------------
--  1.2.2 Replacement Rules  --
-------------------------------

type ReplacementBooleanVariants lex b = 
        ( Typeable b
        , BooleanLanguage (ClassicalSequentOver lex (Form b))
        , BooleanConstLanguage (ClassicalSequentOver lex (Form b))
        , IndexedSchemePropLanguage (ClassicalSequentOver lex (Form b))
        , IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b))
        ) => [SequentRule lex (Form b)]

biconditionalInterchange :: ReplacementBooleanVariants lex b
biconditionalInterchange = [
                [ GammaV 1 :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2 :|-: SS (propCtx 1 (phin 1))
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (propCtx 1 (phin 2))
            ,
                [ GammaV 1 :|-: SS (phin 1 .↔. phin 2)
                , GammaV 2 :|-: SS (propCtx 1 (phin 2))
                ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (propCtx 1 (phin 1))
            ]

replace :: ( Typeable b, IndexedPropContextSchemeLanguage (ClassicalSequentOver lex (Form b))
        ) => ClassicalSequentOver lex (Form b) -> ClassicalSequentOver lex (Form b) -> [SequentRule lex (Form b)]
replace x y = [ [GammaV 1  :|-: SS (propCtx 1 x)] ∴ GammaV 1  :|-: SS (propCtx 1 y)
              , [GammaV 1  :|-: SS (propCtx 1 y)] ∴ GammaV 1  :|-: SS (propCtx 1 x)]

exchange :: Typeable b => ClassicalSequentOver lex (Form b) -> ClassicalSequentOver lex (Form b) -> [SequentRule lex (Form b)]
exchange x y = [ [GammaV 1  :|-: SS x] ∴ GammaV 1  :|-: SS y, [GammaV 1  :|-: SS y] ∴ GammaV 1  :|-: SS x]

andCommutativity :: ReplacementBooleanVariants lex b
andCommutativity = replace (phin 1 ./\. phin 2) (phin 2 ./\. phin 1)

andAssociativity :: ReplacementBooleanVariants lex b
andAssociativity = replace ((phin 1 ./\. phin 2) ./\. phin 3) (phin 1 ./\. (phin 2 ./\. phin 3))

andIdempotence :: ReplacementBooleanVariants lex b
andIdempotence = replace (phin 1 ./\. phin 1) (phin 1)

andDistributivity :: ReplacementBooleanVariants lex b
andDistributivity = replace (phin 1 ./\. (phin 2 .\/. phin 3)) ((phin 1 ./\. phin 2) .\/. (phin 1 ./\. phin 3))
                    ++ replace ((phin 2 .\/. phin 3) ./\. phin 1) ((phin 2 ./\. phin 1) .\/. (phin 3 ./\. phin 1))

orCommutativity :: ReplacementBooleanVariants lex b
orCommutativity = replace (phin 1 .\/. phin 2) (phin 2 .\/. phin 1)

orAssociativity :: ReplacementBooleanVariants lex b
orAssociativity = replace ((phin 1 .\/. phin 2) .\/. phin 3) (phin 1 .\/. (phin 2 .\/. phin 3))

orIdempotence :: ReplacementBooleanVariants lex b
orIdempotence = replace (phin 1 .\/. phin 1) (phin 1)

orDistributivity :: ReplacementBooleanVariants lex b
orDistributivity = replace (phin 1 .\/. (phin 2 ./\. phin 3)) ((phin 1 .\/. phin 2) ./\. (phin 1 .\/. phin 3))
                   ++ replace ((phin 2 ./\. phin 3) .\/. phin 1) ((phin 2 .\/. phin 1) ./\. (phin 3 .\/. phin 1))

iffCommutativity :: ReplacementBooleanVariants lex b
iffCommutativity = replace (phin 1 .<=>. phin 2) (phin 2 .<=>. phin 1)

deMorgansLaws :: ReplacementBooleanVariants lex b
deMorgansLaws = replace (lneg $ phin 1 ./\. phin 2) (lneg (phin 1) .\/. lneg (phin 2))
             ++ replace (lneg $ phin 1 .\/. phin 2) (lneg (phin 1) ./\. lneg (phin 2))

doubleNegatingDeMorgansLaws :: ReplacementBooleanVariants lex b
doubleNegatingDeMorgansLaws = replace (lneg ((lneg $ phin 1) ./\. phin 2)) (phin 1 .\/. lneg (phin 2))
                           ++ replace (lneg ((lneg $ phin 1) .\/. phin 2)) (phin 1 ./\. lneg (phin 2))
                           ++ replace (lneg (phin 1 ./\. (lneg $ phin 2))) (lneg (phin 1) .\/. phin 2)
                           ++ replace (lneg (phin 1 .\/. (lneg $ phin 2))) (lneg (phin 1) ./\. phin 2)
                           ++ replace (lneg ((lneg $ phin 1) ./\. (lneg $ phin 2))) (phin 1 .\/. phin 2)
                           ++ replace (lneg ((lneg $ phin 1) .\/. (lneg $ phin 2))) (phin 1 ./\. phin 2)

doubleNegation :: ReplacementBooleanVariants lex b
doubleNegation = replace (lneg $ lneg $ phin 1) (phin 1)

materialConditional :: ReplacementBooleanVariants lex b
materialConditional = replace (phin 1 .=>. phin 2) (lneg (phin 1) .\/. phin 2)
                   ++ replace (phin 1 .\/. phin 2) (lneg (phin 1) .=>. phin 2)

negatedConditional :: ReplacementBooleanVariants lex b
negatedConditional = replace (lneg $ phin 1 .=>. phin 2) (phin 1 ./\. (lneg $ phin 2))

negatedBiconditional :: ReplacementBooleanVariants lex b
negatedBiconditional = replace (lneg $ phin 1 .<=>. phin 2) (phin 1 .<=>. (lneg $ phin 2))
                    ++ replace (lneg $ phin 1 .<=>. phin 2) ((lneg $ phin 1) .<=>. phin 2)

contraposition :: ReplacementBooleanVariants lex b
contraposition = replace (phin 1 .=>. phin 2) (lneg (phin 2) .=>. lneg (phin 1))

doubleNegatingContraposition :: ReplacementBooleanVariants lex b
doubleNegatingContraposition = replace (lneg (phin 1) .=>. phin 2) (lneg (phin 2) .=>. phin 1)
                            ++ replace (phin 1 .=>. lneg (phin 2)) (phin 2 .=>. lneg (phin 1))

exportation :: ReplacementBooleanVariants lex b
exportation = replace (phin 1 .=>. (phin 2 .=>. phin 3)) ((phin 1 ./\. phin 2) .=>. phin 3)

andAbsorption :: ReplacementBooleanVariants lex b
andAbsorption = replace (phin 1 ./\. (phin 1 .\/. phin 2)) (phin 1)
                ++ replace (phin 1 ./\. (phin 2 .\/. phin 1)) (phin 1)
                ++ replace ((phin 1 .\/. phin 2) ./\. phin 1) (phin 1)
                ++ replace ((phin 2 .\/. phin 1) ./\. phin 1) (phin 1)

orAbsorption :: ReplacementBooleanVariants lex b
orAbsorption = replace (phin 1 .\/. (phin 1 ./\. phin 2)) (phin 1) 
               ++ replace (phin 1 .\/. (phin 2 ./\. phin 1)) (phin 1)
               ++ replace ((phin 1 ./\. phin 2) .\/. phin 1) (phin 1)
               ++ replace ((phin 2 ./\. phin 1) .\/. phin 1) (phin 1)

distribution :: ReplacementBooleanVariants lex b
distribution = andDistributivity ++ orDistributivity

biconditionalExchange :: ReplacementBooleanVariants lex b
biconditionalExchange = replace (phin 1 .<=>. phin 2) ((phin 1 .=>. phin 2) ./\. (phin 2 .=>. phin 1))

biconditionalCases :: ReplacementBooleanVariants lex b
biconditionalCases = replace (phin 1 .<=>. phin 2) ((phin 1 ./\. phin 2) .\/. (lneg (phin 1) ./\. lneg (phin 2)))

andTautCancellation :: ReplacementBooleanVariants lex b
andTautCancellation = replace (phin 1 ./\. (phin 2 .\/. lneg (phin 2))) (phin 1)
                   ++ replace ((phin 2 .\/. lneg (phin 2)) ./\. phin 1) (phin 1)
                   ++ replace (phin 1 ./\. (lneg (phin 2) .\/. phin 2)) (phin 1)
                   ++ replace ((lneg (phin 2) .\/. phin 2) ./\. phin 1) (phin 1)

andContCancellation :: ReplacementBooleanVariants lex b
andContCancellation = replace (phin 1 ./\. (phin 2 ./\. lneg (phin 2))) (phin 2 ./\. lneg (phin 2))
                   ++ replace ((phin 2 ./\. lneg (phin 2)) ./\. phin 1) (phin 2 ./\. lneg (phin 2))
                   ++ replace (phin 1 ./\. (lneg (phin 2) ./\. phin 2)) (lneg (phin 2) ./\. phin 2)
                   ++ replace ((lneg (phin 2) ./\. phin 2) ./\. phin 1) (lneg (phin 2) ./\. phin 2)

orContCancellation :: ReplacementBooleanVariants lex b
orContCancellation = replace (phin 1 .\/. (phin 2 ./\. lneg (phin 2))) (phin 1)
                   ++ replace ((phin 2 ./\. lneg (phin 2)) .\/. phin 1) (phin 1)
                   ++ replace (phin 1 .\/. (lneg (phin 2) ./\. phin 2)) (phin 1)
                   ++ replace ((lneg (phin 2) ./\. phin 2) .\/. phin 1) (phin 1)

orTautCancellation :: ReplacementBooleanVariants lex b
orTautCancellation = replace (phin 1 .\/. (phin 2 .\/. lneg (phin 2))) (phin 2 .\/. lneg (phin 2))
                   ++ replace ((phin 2 .\/. lneg (phin 2)) .\/. phin 1) (phin 2 .\/. lneg (phin 2))
                   ++ replace (phin 1 .\/. (lneg (phin 2) .\/. phin 2)) (lneg (phin 2) .\/. phin 2)
                   ++ replace ((lneg (phin 2) .\/. phin 2) .\/. phin 1) (lneg (phin 2) .\/. phin 2)

----------------------------------------
--  1.2.3 Infinitary Variation Rules  --
----------------------------------------

-- rules with an infnite number of schematic variations

-- XXX at the moment, these requires all assumptions to be used. Should
-- actually be parameterized by l::[Bool] of length n rather than n::Int
-- or alternately, the checking mechanism should be modified to allow
-- weakening.

eliminationOfCases :: Int -> BooleanRule lex b
eliminationOfCases n = (premAnt n :|-: SS lfalsum
                     : take n (map premiseForm [1 ..]))
                     ∴ GammaV 1 :|-: SS (concSuc n)
    where premiseForm m = SA (lneg $ phin m) :|-: SS (lneg $ phin m)
          premAnt m = foldr (:+:) (GammaV 1) (take m $ map (SA . lneg . phin) [1 ..])
          concSuc m = foldr (.∨.) (phin 1) (take (m - 1) $ map phin [2 ..])

-- XXX slight syntactic variation from Hardegree's rule.
separationOfCases :: Int -> BooleanRule lex b
separationOfCases n = (GammaV 0 :|-: SS (premSuc n)
                    : take n (map premiseForm [1 ..]))
                    ∴ concAnt n :|-: SS (phin 0)
    where premSuc m = foldr (.∨.) (phin 1) (take (m - 1) $ map phin [2 ..])
          premiseForm m = GammaV m :+: SA (phin m) :|-: SS (phin 0)
          concAnt m = foldr (:+:) (GammaV 0) (take m $ map GammaV [1 ..])

explicitSeparationOfCases :: Int -> BooleanRule lex b
explicitSeparationOfCases n = (GammaV 0 :|-: SS (premSuc n)
                            : map premiseForm [1 .. n]
                            ++ map assumptionForm [1 .. n])
                            ∴ concAnt n :|-: SS (phin 0)
    where premSuc m = foldr (.∨.) (phin 1) (take (m - 1) $ map phin [2 ..])
          premiseForm m = GammaV m :+: SA (phin m) :|-: SS (phin 0)
          assumptionForm m = SA (phin m) :|-: SS (phin m)
          concAnt m = foldr (:+:) (GammaV 0) (take m $ map GammaV [1 ..])
