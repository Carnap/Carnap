{-#LANGUAGE  FlexibleContexts,  FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Lande where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Control.Lens (view, (^?))
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
import Carnap.Languages.PurePropositional.Logic.Lande hiding (Pr)

data LandeQuant = Prop LandeProp
               | UI    | UE
               | EI    | EE
               | EqI   | EqE 
               | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
               deriving Eq

instance Show LandeQuant where
        show (Prop x) = show x
        show EI = "∃I"
        show EE = "∃E"
        show UI = "∀I"
        show UE = "∀E"
        show EqI = "=I"
        show EqE = "=E"

instance Inference LandeQuant PureLexiconFOL (Form Bool) where

        ruleOf (Pr _) = axiom
        ruleOf UI  = universalGeneralization
        ruleOf UE  = universalInstantiation
        ruleOf EI  = existentialGeneralization
        ruleOf EE  = conditionalExistentialDerivation
        ruleOf EqI = eqReflexivity
        ruleOf EqE = leibnizLawVariations !! 0 --do we also want reverse?
        ruleOf r = premisesOf r ∴ conclusionOf r

        premisesOf (Prop x) = map liftSequent (premisesOf x)
        premisesOf x = upperSequents (ruleOf x)

        conclusionOf (Prop x) = liftSequent (conclusionOf x)
        conclusionOf x = lowerSequent (ruleOf x)

        restriction UI = Just (eigenConstraint tau (SS (lall "v" $ phi' 1)) (fogamma 1) 
                              `andFurtherRestriction` variableOnlyConstraint)
        restriction EE = Just (eigenConstraint tau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2)
                              `andFurtherRestriction` variableOnlyConstraint)
        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        globalRestriction (Left ded) n (Prop CP) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (Prop CP)))
        globalRestriction (Left ded) n (Prop RAA1) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (Prop RAA1)))
        globalRestriction (Left ded) n (Prop RAA2) = Just (dischargeConstraint n ded (view lhs $ conclusionOf (Prop RAA2)))
        globalRestriction _ _ _ = Nothing

        indirectInference (Prop x) = indirectInference x
        indirectInference _ = Nothing

        isAssumption (Pr _) = True
        isAssumption (Prop x) = isAssumption x
        isAssumption _ = False

variableOnlyConstraint  sub | isVar t = Nothing
                            | otherwise = Just "You appear to be using a constant when you should be using a variable"
    where isVar x = case x ^? _varLabel of
                  Nothing -> False
                  Just _ -> True
          t = applySub sub tau


parseLandeQuant rtc n annote = try parseQuant <|> parseProp 
    where parseProp = map Prop <$> parseLandeProp defaultRuntimeDeductionConfig n annote
          parseQuant = do r <- choice (map (try . string) [ "AI","∀I", "AE","∀E", "EE", "∃E",  "EI", "∃I", "=I", "=E" ])
                          return $ case r of
                                      _ | r `elem` ["∀I", "AI"] -> [UI]
                                        | r `elem` ["∀E", "AE"] -> [UE]
                                        | r `elem` ["∃E", "EE"] -> [EE]
                                        | r `elem` ["∃I", "EI"] -> [EI]
                                      "=I" -> [EqI]
                                      "=E" -> [EqE]

parseLandeQuantProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) 
                     -> String -> [DeductionLine LandeQuant PureLexiconFOL (Form Bool)]
parseLandeQuantProof rtc = toDeductionLemmon (parseLandeQuant rtc) landeQuantFormulaParser

--TODO: drop outer parens, redraw quantificational phrases
landeQuantNotation :: String -> String 
landeQuantNotation x = case runParser altparser 0 "" x of
                            Left e -> show e
                            Right s -> s
    where altparser = do s <- try handleQuant <|> handleCon <|> try handleAtom <|> try handleSchema <|> fallback
                         rest <- (eof >> return "") <|> altparser
                         return $ s ++ rest
          handleQuant = do q <- oneOf "∀∃"
                           v <- anyChar
                           return $ "(" ++ [q,v] ++ ")"
          handleSchema = (char 'φ' >> return "◯")
                  <|> (char 'ψ' >> return "□")
                  <|> (char 'χ' >> return "△")
          handleCon = (char '¬' >> return "-")
                  <|> (char '⊤' >> return " ")
                  <|> (char '∅' >> return " ")
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          fallback = do c <- anyChar 
                        return [c]

landeQuantCalc = mkNDCalc
    { ndRenderer = LemmonStyle StandardLemmon
    , ndParseProof = parseLandeQuantProof
    , ndProcessLine = hoProcessLineLemmon
    , ndProcessLineMemo = Just hoProcessLineLemmonMemo
    , ndParseForm = landeQuantFormulaParser
    , ndParseSeq = parseSeqOver landeQuantFormulaParser
    , ndNotation = landeQuantNotation . dropOuterParens
    }
