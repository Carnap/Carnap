{-#LANGUAGE GADTs, FlexibleContexts, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.Rules where

import Data.List (intercalate)
import Text.Parsec
import Carnap.Core.Data.Util (scopeHeight)
import Carnap.Core.Unification.Unification (applySub,subst)
import Carnap.Core.Data.AbstractSyntaxClasses
import Carnap.Core.Data.AbstractSyntaxDataTypes
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.Util.LanguageClasses
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

ss :: PureFOLForm -> FOLSequentCalc Succedent
ss = SS . liftToSequent

sa :: PureFOLForm -> FOLSequentCalc Antecedent
sa = SA . liftToSequent

phi n x = PPhi n AOne AOne :!$: x

tau = taun 1

tau' = taun 2

data DerivedRule = DerivedRule { conclusion :: PureFOLForm, premises :: [PureFOLForm]}
               deriving (Show, Eq)

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
--  1.2. Rules with Variations  --
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
                            [ GammaV 1 :+:  sa (phi 1 tau) :|-: ss (phin 1) 
                            , GammaV 2 :|-: ss (PBind (Some "v") $ phi 1)   
                            , sa (phi 1 tau) :|-: ss (phi 1 tau)            
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: ss (phin 1)      
                        ,
                            [ GammaV 1 :|-: ss (phin 1)
                            , sa (phi 1 tau) :|-: ss (phi 1 tau)
                            , GammaV 2 :|-: ss (PBind (Some "v") $ phi 1)
                            ] ∴ GammaV 1 :+: GammaV 2 :|-: ss (phin 1)
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
