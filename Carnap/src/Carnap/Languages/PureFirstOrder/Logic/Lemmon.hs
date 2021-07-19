{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Lemmon where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Control.Lens (view)
import Carnap.Core.Data.Types 
import Carnap.Core.Data.Classes
import Carnap.Core.Unification.Unification (applySub,occurs)
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules (dischargeConstraint, premConstraint,axiom)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Lemmon hiding (Pr)

data LemmonQuant = Prop LemmonProp
               | UI    | UE
               | EI    | EE
               | EqI   | EqE 
               | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
               deriving Eq

instance Show LemmonQuant where
        show (Prop x) = show x
        show EI = "EI"
        show EE = "EE"
        show UI = "UI"
        show UE = "UE"
        show EqI = "=I"
        show EqE = "=E"

instance Inference LemmonQuant PureLexiconFOL (Form Bool) where

        ruleOf (Pr _) = axiom
        ruleOf UI  = universalGeneralization
        ruleOf UE  = universalInstantiation
        ruleOf EI  = existentialGeneralization
        ruleOf EE  = existentialDerivation !! 0
        ruleOf EqI = eqReflexivity
        ruleOf EqE = leibnizLawVariations !! 0 --do we also want reverse?
        ruleOf r = premisesOf r ∴ conclusionOf r

        premisesOf (Prop x) = map liftSequent (premisesOf x)
        premisesOf x = upperSequents (ruleOf x)

        conclusionOf (Prop x) = liftSequent (conclusionOf x)
        conclusionOf x = lowerSequent (ruleOf x)

        restriction UI = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1))
        restriction EE = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n EE = Just (dischargeConstraint n ded (view lhs $ conclusionOf EE))
        globalRestriction (Left ded) n (Prop CP) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (Prop CP)))
        globalRestriction (Left ded) n (Prop RAA1) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (Prop RAA1)))
        globalRestriction (Left ded) n (Prop RAA2) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (Prop RAA2)))
        globalRestriction (Left ded) n (Prop ORE) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (Prop ORE)))
        globalRestriction _ _ _ = Nothing

        indirectInference (Prop x) = indirectInference x
        indirectInference EE = Just $ TypedProof (ProofType 1 1)
        indirectInference _ = Nothing

        isAssumption (Pr _) = True
        isAssumption (Prop x) = isAssumption x
        isAssumption _ = False

parseLemmonQuant rtc n annote = try parseProp <|> parseQuant
    where parseProp = map Prop <$> parseLemmonProp defaultRuntimeDeductionConfig n annote
          parseQuant = do r <- choice (map (try . string) [ "UI", "UE", "EE", "EI", "=I", "=E" ])
                          return $ case r of
                                      "UI" -> [UI]
                                      "UE" -> [UE]
                                      "EE" -> [EE]
                                      "EI" -> [EI]
                                      "=I" -> [EqI]
                                      "=E" -> [EqE]

parseLemmonQuantProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) 
                     -> String -> [DeductionLine LemmonQuant PureLexiconFOL (Form Bool)]
parseLemmonQuantProof rtc = toDeductionLemmon (parseLemmonQuant rtc) lemmonQuantFormulaParser

--TODO: drop outer parens, redraw quantificational phrases
lemmonQuantNotation :: String -> String 
lemmonQuantNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> s
    where altparser = do s <- try handleQuant <|> handlecon <|> try handleatom <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handleQuant = do q <- oneOf "∀∃"
                           v <- anyChar
                           return $ "(" ++ (if q == '∃' then "∃" else "") ++ [v] ++ ")"
          handlecon = (char '∧' >> return "&")
                  <|> (char '¬' >> return "-")
          handleatom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          fallback = do c <- anyChar 
                        return [c]

lemmonQuantCalc = mkNDCalc
    { ndRenderer = LemmonStyle StandardLemmon
    , ndParseProof = parseLemmonQuantProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseForm = lemmonQuantFormulaParser
    , ndParseSeq = parseSeqOver lemmonQuantFormulaParser
    , ndNotation = lemmonQuantNotation . dropOuterParens
    }
