{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.KalishAndMontegue
        (FOLogic(..), parseFOLogic, folCalc)
    where

import Data.Map as M (lookup, Map,empty)
import Text.Parsec
import Carnap.Core.Data.AbstractSyntaxDataTypes (Form)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLine, hoProcessLineMemo, hoProcessLineFitch)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericConnectives
import Carnap.Languages.PureFirstOrder.Logic.Rules

--------------------------------------------------------
--2. Classical First-Order Logic
--------------------------------------------------------

data FOLogic =  SL P.PropLogic
                | UD  | UI  | EG  | ED1  | ED2  | DER DerivedRule
                | QN1 | QN2 | QN3 | QN4
               deriving (Eq)

instance Show FOLogic where
        show UD      = "UD"
        show UI      = "UI"
        show EG      = "EG"
        show ED1     = "ED"
        show ED2     = "ED"
        show (DER _) = "Derived"
        show QN1     = "QN"
        show QN2     = "QN"
        show QN3     = "QN"
        show QN4     = "QN"
        show (SL x)  = show x

-- TODO use liftSequent to clean this up
instance Inference FOLogic PureLexiconFOL where
     ruleOf UI        = universalInstantiation
     ruleOf EG        = existentialGeneralization
     ruleOf UD        = universalGeneralization
     ruleOf ED1       = existentialDerivation !! 0
     ruleOf ED2       = existentialDerivation !! 1
     ruleOf QN1       = quantifierNegation !! 0
     ruleOf QN2       = quantifierNegation !! 1
     ruleOf QN3       = quantifierNegation !! 2
     ruleOf QN4       = quantifierNegation !! 3

     premisesOf (SL x) = map liftSequent (premisesOf x)
     premisesOf (DER r) = zipWith gammafy (premises r) [1..]
        where gammafy p n = GammaV n :|-: SS (liftToSequent p)
     
     premisesOf x     = upperSequents (ruleOf x)

     conclusionOf (SL x) = liftSequent (conclusionOf x)
     conclusionOf (DER r) = gammas :|-: SS (liftToSequent $ conclusion r)
        where gammas = foldl (:+:) Top (map GammaV [1..length (premises r)])
     conclusionOf x   = lowerSequent (ruleOf x)

     restriction UD     = Just (eigenConstraint (SeqT 1) (ss (PBind (All "v") $ phi 1)) (GammaV 1))
     restriction ED1    = Just (eigenConstraint (SeqT 1) (ss (PBind (Some "v") $ phi 1) :-: ss (phin 1)) (GammaV 1 :+: GammaV 2))
     restriction ED2    = Nothing --Since this one does not use the assumption with a fresh object
     restriction _      = Nothing

     indirectInference (SL x) = indirectInference x
     indirectInference x
        | x `elem` [ ED1,ED2 ] = Just PolyProof
        | otherwise = Nothing


parseFOLogic :: Map String DerivedRule -> Parsec String u [FOLogic]
parseFOLogic ders = try quantRule <|> liftProp
    where liftProp = do r <- P.parsePropLogic M.empty
                        return (map SL r)
          quantRule = do r <- choice (map (try . string) [ "UI", "UD", "EG", "ED", "QN","D-"])
                         case r of 
                            r | r == "UI" -> return [UI]
                              | r == "UD" -> return [UD]
                              | r == "EG" -> return [EG]
                              | r == "ED" -> return [ED1,ED2]
                              | r == "QN" -> return [QN1,QN2,QN3,QN4]
                              | r == "D-" ->  do rn <- many1 upper
                                                 case M.lookup rn ders of
                                                    Just r  -> return [DER r]
                                                    Nothing -> parserFail "Looks like you're citing a derived rule that doesn't exist"

parseFOLProof ::  Map String DerivedRule -> String -> [DeductionLine FOLogic PureLexiconFOL (Form Bool)]
parseFOLProof ders = toDeduction (parseFOLogic ders) folFormulaParser

folCalc = NaturalDeductionCalc
    { ndRenderer = MontegueStyle
    , ndParseProof = parseFOLProof
    , ndProcessLine = hoProcessLine
    , ndProcessLineMemo = Just hoProcessLineMemo
    , ndParseSeq = folSeqParser
    }
