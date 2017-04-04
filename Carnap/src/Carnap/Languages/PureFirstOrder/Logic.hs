{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic
        (FOLogic(..), parseFOLogic,parseForallxQL, parseFOLProof, folSeqParser, phiS, phi, tau, ss, FOLSequentCalc, DerivedRule(..))
    where

import Data.Map as M (lookup, Map,empty)
import Data.List (intercalate)
import Text.Parsec
import Carnap.Core.Data.Util (scopeHeight)
--import Carnap.Core.Util
import Carnap.Core.Unification.Unification
--import Carnap.Core.Unification.Combination
import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import qualified Carnap.Languages.PurePropositional.Logic as P
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.GenericConnectives

--------------------------------------------------------
--1. FirstOrder Sequent Calculus
--------------------------------------------------------

type FOLSequentCalc = ClassicalSequentOver PureLexiconFOL

--we write the Copula schema at this level since we may want other schemata
--for sequent languages that contain things like quantifiers
instance CopulaSchema FOLSequentCalc where 

    appSchema (SeqQuant (All x)) (LLam f) e = schematize (All x) (show (f $ SeqV x) : e)
    appSchema (SeqQuant (Some x)) (LLam f) e = schematize (Some x) (show (f $ SeqV x) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema f [] = "λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h)))
        where h = scopeHeight (LLam f)
    lamSchema f (x:xs) = "(λβ_" ++ show h ++ "." ++ show (f (SeqSV (-1 * h))) ++ intercalate " " (x:xs) ++ ")"
        where h = scopeHeight (LLam f)

pattern SeqQuant q        = FX (Lx2 (Lx1 (Lx2 (Bind q))))
pattern SeqSV n           = FX (Lx2 (Lx1 (Lx1 (Lx4 (StaticVar n)))))
pattern SeqVar c a        = FX (Lx2 (Lx1 (Lx4 (Function c a))))
pattern SeqTau c a        = FX (Lx2 (Lx1 (Lx5 (Function c a))))
pattern SeqV s            = SeqVar (Var s) AZero
pattern SeqT n            = SeqTau (SFunc AZero n) AZero

instance Eq (FOLSequentCalc a) where
        (==) = (=*)

instance ParsableLex (Form Bool) PureLexiconFOL where
        langParser = folFormulaParser

folSeqParser = seqFormulaParser :: Parsec String u (FOLSequentCalc Sequent)

-------------------------
--  1.1. Common Rules  --
-------------------------

eqReflexivity = [] ∴ Top :|-: ss (tau :==: tau)

universalGeneralization = [ GammaV 1 :|-: ss (phi 1 tau)]
                          ∴ GammaV 1 :|-: ss (PBind (All "v") (phi 1))

universalInstantiation = [ GammaV 1 :|-: ss (PBind (All "v") (phi 1))]
                         ∴ GammaV 1 :|-: ss (phi 1 tau)

existentialGeneralization = [ GammaV 1 :|-: ss (phi 1 tau)]
                            ∴ GammaV 1 :|-: ss (PBind (Some "v") (phi 1))

------------------------------------
--  1.1.2. Rules with Variations  --
------------------------------------

leibnizLawVariations = [
                           [ GammaV 1 :|-: ss (phi 1 tau)
                           , GammaV 2 :|-: ss (tau :==: tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: ss (phi 1 tau')
                       , 
                           [ GammaV 1 :|-: ss (phi 1 tau')
                           , GammaV 2 :|-: ss (tau :==: tau')
                           ] ∴ GammaV 1 :+: GammaV 2 :|-: ss (phi 1 tau)
                       ]

existentialDerivation = [
                            [ GammaV 1 :+:  sa (phi 1 tau) :|-: ss (phiS 1) 
                            , GammaV 2 :|-: ss (PBind (Some "v") $ phi 1)   
                            , sa (phi 1 tau) :|-: ss (phi 1 tau)            
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: ss (phiS 1)      
                        ,
                            [ GammaV 1 :|-: ss (phiS 1)
                            , sa (phi 1 tau) :|-: ss (phi 1 tau)
                            , GammaV 2 :|-: ss (PBind (Some "v") $ phi 1)
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: ss (phiS 1)
                        ]

quantifierNegation = [  
                        [ GammaV 1 :|-: ss (PNeg $ PBind (Some "v") $ phi 1)] 
                        ∴ GammaV 1 :|-: ss (PBind (All "v") $ \x -> PNeg $ phi 1 x)
                     ,  [ GammaV 1 :|-: ss (PBind (Some "v") $ \x -> PNeg $ phi 1 x)] 
                        ∴ GammaV 1 :|-: ss (PNeg $ PBind (All "v")  $ phi 1)
                     ,  [ GammaV 1 :|-: ss (PNeg $ PBind (All "v") $ phi 1)] 
                        ∴ GammaV 1 :|-: ss (PBind (Some "v") $ \x -> PNeg $ phi 1 x)
                     ,  [ GammaV 1 :|-: ss (PBind (All "v") $ \x -> PNeg $ phi 1 x)] 
                        ∴ GammaV 1 :|-: ss (PNeg $ PBind (Some "v") $ phi 1)
                     ]

--------------------------------------------------------
--2. Classical First-Order Logic
--------------------------------------------------------

data DerivedRule = DerivedRule { conclusion :: PureFOLForm, premises :: [PureFOLForm]}
               deriving (Show, Eq)

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

ss :: PureFOLForm -> FOLSequentCalc Succedent
ss = SS . liftToSequent

sa :: PureFOLForm -> FOLSequentCalc Antecedent
sa = SA . liftToSequent

phiS n = PPhi n AZero AZero

phi n x = PPhi n AOne AOne :!$: x

tau = PT 1

tau' = PT 2

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
     restriction ED1    = Just (eigenConstraint (SeqT 1) (ss (PBind (Some "v") $ phi 1) :-: ss (phiS 1)) (GammaV 1 :+: GammaV 2))
     restriction ED2    = Nothing --Since this one does not use the assumption with a fresh object
     restriction _      = Nothing

     indirectInference (SL x) = indirectInference x
     indirectInference x
        | x `elem` [ ED1,ED2 ] = Just PolyProof
        | otherwise = Nothing

eigenConstraint c suc ant sub
    | c' `occursIn` ant' = Just $ "The constant " ++ show c' ++ " appears not to be fresh, given that this line relies on " ++ show ant'
    | c' `occursIn` suc' = Just $ "The constant " ++ show c' ++ " appears not to be fresh in the other premise " ++ show suc'
    | otherwise = case fromSequent c' of 
                          PC _ -> Nothing
                          PT _ -> Nothing
                          _ -> Just $ "The term " ++ show c' ++ " is not a constant"
    where c'   = applySub sub c
          ant' = applySub sub ant
          suc' = applySub sub suc
          -- XXX : this is not the most efficient way of checking
          -- imaginable.
          occursIn x y = not $ (subst x (static 0) y) =* y

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

--------------------
--  3. System QL  --
--------------------
-- A system of first-order logic resembling system QL from PD Magnus'
-- forallx

data ForallxQL = ForallxSL P.ForallxSL | UIX | UEX | EIX | EE1X | EE2X | IDIX | IDE1X | IDE2X
                    deriving (Show, Eq)

instance Inference ForallxQL PureLexiconFOL where

         ruleOf UIX   = universalInstantiation
         ruleOf UEX   = universalInstantiation
         ruleOf EIX   = existentialGeneralization
         ruleOf EE1X  = existentialDerivation !! 0 
         ruleOf EE2X  = existentialDerivation !! 1 
         ruleOf IDIX  = eqReflexivity

         ruleOf IDE1X  = leibnizLawVariations !! 0
         ruleOf IDE2X  = leibnizLawVariations !! 1

         premisesOf (ForallxSL x) = map liftSequent (premisesOf x)
         premisesOf r = upperSequents (ruleOf r)
         
         conclusionOf (ForallxSL x) = liftSequent (conclusionOf x)
         conclusionOf r = lowerSequent (ruleOf r)

         indirectInference (ForallxSL x) = indirectInference x
         indirectInference x  
            | x `elem` [ EE1X,EE2X ] = Just AssumptiveProof
            | otherwise = Nothing

         restriction UIX    = Just (eigenConstraint (SeqT 1) (ss (PBind (All "v") $ phi 1)) (GammaV 1))
         restriction EE1X   = Just (eigenConstraint (SeqT 1) (ss (PBind (Some "v") $ phi 1) :-: ss (phiS 1)) (GammaV 1 :+: GammaV 2))
         restriction EE2X   = Nothing --Since this one does not use the assumption with a fresh object
         restriction _      = Nothing

parseForallxQL ders = try liftProp <|> quantRule
    where liftProp = do r <- P.parseForallxSL ders
                        return (map ForallxSL r)
          quantRule = do r <- choice (map (try . string) ["∀I", "AI", "∀E", "AE", "∃I", "EI", "∃E", "EE", "=I","=E" ])
                         case r of 
                            r | r `elem` ["∀I","AI"] -> return [UIX]
                              | r `elem` ["∀E","AE"] -> return [UEX]
                              | r `elem` ["∃I","EI"] -> return [EIX]
                              | r `elem` ["∃E","EE"] -> return [EE1X, EE2X]
                              | r == "=I" -> return [IDIX]
                              | r == "=E" -> return [IDE1X,IDE2X]
